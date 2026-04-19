/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.CryptoFoundations.SeededFork
import VCVio.CryptoFoundations.ReplayFork

set_option linter.style.longFile 3200

/-!
# EUF-CMA security of the Fiat-Shamir Σ-protocol transform

End-to-end security reduction, packaged as three theorems:

- `euf_cma_to_nma`: CMA-to-NMA via HVZK simulation, absorbing the signing-query
  loss into a statistical term `qS · ζ_zk + ζ_col`;
- `euf_nma_bound`: NMA-to-extraction via `Fork.replayForkingBound` and special
  soundness, producing a reduction to `hardRelationExp`;
- `euf_cma_bound`: the combined bound, instantiating `euf_cma_to_nma` into
  `euf_nma_bound`.
-/

universe u v

open OracleComp OracleSpec
open scoped ENNReal

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-- Birthday-bound collision slack for the Fiat-Shamir CMA-to-NMA reduction.

For `qS` signing queries, `qH` random-oracle queries, and simulator commitment
predictability `β` (i.e. `∀ c₀, Pr[commit = c₀] ≤ β`), the probability that the HVZK
simulator tries to program a cache entry `(msg, c)` already populated by a prior query
is bounded by `qS · (qS + qH) · β` via the birthday/union bound.

Matches EasyCrypt's `pr_bad_game` at
[fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) (`QS · (QS+QR) / |Ω|`
with `β = 1/|Ω|` for Schnorr) and plays the same role as `GPVHashAndSign.collisionBound`
for the PSF construction. -/
noncomputable def collisionSlack (qS qH : ℕ) (β : ℝ≥0∞) : ℝ≥0∞ :=
  (qS * (qS + qH) : ℕ) * β

/-!
### Components of the CMA-to-NMA simulator

The reduction runs the CMA adversary inside a `StateT`-carried cache (`QueryCache`) over
the combined oracle spec `unifSpec + (M × Commit →ₒ Chal)`. The four simulator layers
below (`fwdImpl`, `unifSimImpl`, `roSimImpl`, `baseSimImpl`, `sigSimImpl`) are the same
objects that appear locally inside `euf_cma_to_nma`; hoisting them lets us split the
main proof into a sequence of smaller lemmas (Phase B / Phase C / Phase D).

All live in `namespace FiatShamir` with the ambient variables `σ hr M`; callers supply
the challenge/commitment types and the appropriate `DecidableEq` instances.
-/

section NmaReduction

/-- Forwarding query implementation: each hash or unif query is forwarded to the
outer `OracleComp` monad, threading the cache state unchanged. -/
noncomputable def fwdImpl : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
    (StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
      (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
  (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget _

/-- Uniform-spec forwarder (restriction of `fwdImpl` to the left summand). -/
noncomputable def unifSimImpl : QueryImpl unifSpec
    (StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
      (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
  fun n => fwdImpl (M := M) (Commit := Commit) (Chal := Chal) (.inl n)

/-- Caching random-oracle simulator for the NMA side: on a cache hit return the
stored value, otherwise forward to the outer RO and cache the result. -/
noncomputable def roSimImpl [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (M × Commit →ₒ Chal)
      (StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
  fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none =>
        let v ← fwdImpl (M := M) (Commit := Commit) (Chal := Chal) (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)

/-- Base simulator combining the unif forwarder and the caching RO simulator. -/
noncomputable def baseSimImpl [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
  unifSimImpl (M := M) (Commit := Commit) (Chal := Chal) +
    roSimImpl (M := M) (Commit := Commit) (Chal := Chal)

/-- HVZK-based signing-oracle simulator. For each adversary signing query on `msg`,
sample a transcript `(c, ω, s)` from `simTranscript pk` and program the cache entry
`(msg, c) ↦ ω`, overwriting any prior local cache contents at that point. The
simulator is parameterised over
the public key `pk : Stmt`. -/
noncomputable def sigSimImpl [DecidableEq M] [DecidableEq Commit]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (M →ₒ (Commit × Resp))
      (StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
  fun msg => do
    let (c, ω, s) ← simulateQ (unifSimImpl (M := M) (Commit := Commit) (Chal := Chal))
      (simTranscript pk)
    modifyGet fun cache => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)

/-- The managed-RO NMA adversary obtained from an EUF-CMA adversary `adv` by running
`adv.main pk` with real signing replaced by the HVZK simulator `sigSimImpl`. The
returned `QueryCache` is the advice cache delivered back to `managedRoNmaExp`. -/
noncomputable def nmaAdvFromHVZK [DecidableEq M] [DecidableEq Commit]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
  ⟨fun pk => (simulateQ (baseSimImpl (M := M) (Commit := Commit) (Chal := Chal) +
    sigSimImpl (M := M) simTranscript pk) (adv.main pk)).run ∅⟩

/-- Common trace shared by the real CMA experiment (`unforgeableExp`) and the
freshness-dropped Game 1: sample `(pk, sk)`, run `adv.main pk` with real signing,
verify the forgery, and return the pair `(log.wasQueried msg, verified)`.

- Game 0 (`unforgeableExp`) post-composes with `fun p => !p.1 && p.2`.
- Game 1 (freshness-dropped) post-composes with `Prod.snd`.

The internal `letI : DecidableEq M := Classical.decEq _` and
`letI : DecidableEq (Commit × Resp) := Classical.decEq _` match the pattern used by
`SignatureAlg.unforgeableExp`, so `QueryLog.wasQueried` resolves to the same instance
in both computations. -/
noncomputable def cmaCommonBlock [DecidableEq M] [DecidableEq Commit]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Bool × Bool) :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq (Commit × Resp) := Classical.decEq _
  let sigAlg : SignatureAlg (OracleComp (unifSpec + (M × Commit →ₒ Chal))) M Stmt Wit
      (Commit × Resp) :=
    FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M
  do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (unifSpec + (M × Commit →ₒ Chal) + (M →ₒ (Commit × Resp)))
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
      (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget
          (WriterT (QueryLog (M →ₒ (Commit × Resp)))
            (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (OracleComp (unifSpec + (M × Commit →ₒ Chal))) (M × Commit × Resp) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ_fg), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ_fg
    pure (log.wasQueried msg, verified)

end NmaReduction

section NmaPhases

variable [DecidableEq M] [DecidableEq Commit] [Fintype Chal] [SampleableType Chal]
  (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
  (ζ_zk : ℝ)
  (adv : SignatureAlg.unforgeableAdv
    (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))

private abbrev PhaseCCache :
    Type :=
  (unifSpec + (M × Commit →ₒ Chal)).QueryCache

private abbrev PhaseCSignLog :
    Type :=
  QueryLog (M →ₒ (Commit × Resp))

/-- Internal Phase C state:
- `visibleCache` tracks the live random-oracle table actually populated by forwarded hash queries.
- `overlayCache` is the simulator-side programmed table used after signing queries.
- `signLog` records which messages were signed, so the freshness bit remains available.
- `bad` marks the cache/programming collision branch. -/
private structure PhaseCState where
  visibleCache : PhaseCCache (M := M) (Commit := Commit) (Chal := Chal)
  overlayCache : PhaseCCache (M := M) (Commit := Commit) (Chal := Chal)
  signLog : PhaseCSignLog (M := M) (Commit := Commit) (Resp := Resp)
  bad : Bool

private def phaseCInitState :
    PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) :=
  { visibleCache := ∅
    overlayCache := ∅
    signLog := []
    bad := false }

private noncomputable def phaseCWasSigned
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) (msg : M) :
    Bool :=
  letI : DecidableEq (Commit × Resp) := Classical.decEq _
  st.signLog.wasQueried msg

private noncomputable def phaseCHashLookup
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    (mc : M × Commit) : Option Chal :=
  if phaseCWasSigned (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st mc.1 then
    match st.overlayCache (.inr mc) with
    | some ω => some ω
    | none => st.visibleCache (.inr mc)
  else
    st.visibleCache (.inr mc)

private def phaseCRecordHash
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    (mc : M × Commit) (ω : Chal) :
    PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) :=
  { st with
      visibleCache := st.visibleCache.cacheQuery (.inr mc) ω
      overlayCache := st.overlayCache.cacheQuery (.inr mc) ω }

private noncomputable def phaseCAgreesAwayFromSigned
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) : Prop :=
  ∀ msg c,
    phaseCWasSigned (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st msg = false →
      st.overlayCache (.inr (msg, c)) = st.visibleCache (.inr (msg, c))

private noncomputable def phaseCOverlayInvariant
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) : Prop :=
  st.visibleCache ≤ st.overlayCache ∧
    phaseCAgreesAwayFromSigned (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st

private def phaseCBad
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) : Prop :=
  st.bad = true

local notation "PhaseCOuterSpec" => (unifSpec + (M × Commit →ₒ Chal))
local notation "PhaseCFullSpec" => (PhaseCOuterSpec + (M →ₒ (Commit × Resp)))

private def phaseCUnifImpl :
    QueryImpl unifSpec
      (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun n => liftM (query (spec := PhaseCOuterSpec) (.inl n))

private noncomputable def phaseCHashImpl :
    QueryImpl (M × Commit →ₒ Chal)
      (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun mc => do
    let st ← get
    match phaseCHashLookup (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st mc with
    | some ω => pure ω
    | none =>
        let ω ← liftM (query (spec := PhaseCOuterSpec) (.inr mc))
        set (phaseCRecordHash (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st mc ω)
        pure ω

private noncomputable def phaseCBaseImpl :
    QueryImpl PhaseCOuterSpec
      (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  phaseCUnifImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
    phaseCHashImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)

private noncomputable def phaseCHit
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    (mc : M × Commit) : Bool :=
  match phaseCHashLookup (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st mc with
  | some _ => true
  | none => false

private structure PhaseCResult where
  bad : Bool
  wasSigned : Bool
  verified : Bool

private def PhaseCResult.freshSuccess (r : PhaseCResult) : Bool :=
  !r.wasSigned && r.verified

private def PhaseCResult.badOrFreshSuccess (r : PhaseCResult) : Bool :=
  r.bad || r.freshSuccess

private noncomputable def phaseCResultOf
    (st : PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    (msg : M) (verified : Bool) : PhaseCResult :=
  { bad := st.bad
    wasSigned := phaseCWasSigned (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st msg
    verified := verified }

private noncomputable def phaseCRealSignImpl (pk : Stmt) (sk : Wit) :
    QueryImpl (M →ₒ (Commit × Resp))
      (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun msg => do
    let (c, e) ← simulateQ
      (phaseCUnifImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (σ.commit pk sk)
    let st ← get
    let hit := phaseCHit (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st (msg, c)
    let ω ← phaseCHashImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (msg, c)
    let s ← simulateQ
      (phaseCUnifImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (σ.respond pk sk e ω)
    modify fun st =>
      { st with
          overlayCache := st.overlayCache.cacheQuery (.inr (msg, c)) ω
          signLog := st.signLog.logQuery msg (c, s)
          bad := st.bad || hit }
    pure (c, s)

private noncomputable def phaseCSimSignImpl (pk : Stmt) :
    QueryImpl (M →ₒ (Commit × Resp))
      (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun msg => do
    let (c, ω, s) ← simulateQ
      (phaseCUnifImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (simTranscript pk)
    let st ← get
    let hit := phaseCHit (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st (msg, c)
    modify fun st =>
      { st with
          overlayCache := st.overlayCache.cacheQuery (.inr (msg, c)) ω
          signLog := st.signLog.logQuery msg (c, s)
          bad := st.bad || hit }
    pure (c, s)

private noncomputable def realPhaseCExp : SPMF PhaseCResult :=
  (runtime M).evalDist do
    let sigAlg : SignatureAlg (OracleComp PhaseCOuterSpec) M Stmt Wit (Commit × Resp) :=
      FiatShamir (m := OracleComp PhaseCOuterSpec) σ hr M
    let (pk, sk) ← sigAlg.keygen
    let realImpl : QueryImpl PhaseCFullSpec
        (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
          (OracleComp PhaseCOuterSpec)) :=
      phaseCBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
        phaseCRealSignImpl (σ := σ) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk
    let ((msg, sig), st) ←
      (simulateQ realImpl (adv.main pk)).run
        (phaseCInitState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    let verified ← (simulateQ
      (phaseCBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (sigAlg.verify pk msg sig)).run' st
    pure (phaseCResultOf (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st msg verified)

private noncomputable def simPhaseCExp : SPMF PhaseCResult :=
  (runtime M).evalDist do
    let sigAlg : SignatureAlg (OracleComp PhaseCOuterSpec) M Stmt Wit (Commit × Resp) :=
      FiatShamir (m := OracleComp PhaseCOuterSpec) σ hr M
    let (pk, _) ← sigAlg.keygen
    let simImpl : QueryImpl PhaseCFullSpec
        (StateT (PhaseCState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
          (OracleComp PhaseCOuterSpec)) :=
      phaseCBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
        phaseCSimSignImpl (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) simTranscript pk
    let ((msg, sig), st) ←
      (simulateQ simImpl (adv.main pk)).run
        (phaseCInitState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    let verified ← (simulateQ
      (phaseCBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (sigAlg.verify pk msg sig)).run' st
    pure (phaseCResultOf (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) st msg verified)

omit [SampleableType Stmt] [SampleableType Wit] [Fintype Chal] in
/-- **Phase B (freshness drop).**
The CMA advantage of `adv` is bounded above by the probability that verification
succeeds on the `cmaCommonBlock` trace, ignoring the freshness check
`!log.wasQueried msg`. This is the game hop Game 0 → Game 1.

Proved by expressing the CMA experiment as
`(fun p => !p.1 && p.2) <$> cmaCommonBlock` and monotonicity of `probEvent`
against the logical implication `!b && v = true → v = true`. -/
lemma adv_advantage_le_game1 :
    adv.advantage (runtime M) ≤
      Pr[= true | Prod.snd <$> (runtime M).evalDist (cmaCommonBlock σ hr M adv)] := by
  have hCma :
      SignatureAlg.unforgeableExp (runtime M) adv =
        (fun p : Bool × Bool => !p.1 && p.2) <$>
          (runtime M).evalDist (cmaCommonBlock σ hr M adv) := by
    rw [← runtime_evalDist_map]
    change (runtime M).evalDist _ = (runtime M).evalDist _
    congr 1
    simp only [cmaCommonBlock, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_def]
  unfold SignatureAlg.unforgeableAdv.advantage
  rw [hCma, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  refine probEvent_mono (fun p _ hp => ?_)
  rcases p with ⟨b1, b2⟩
  simp only [Function.comp_apply, Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
  exact hp.2

/-!
#### Phase C: freshness-aware hybrid

Phase C keeps the EUF-CMA freshness bit all the way through the simulator
replacement. The real experiment is re-expressed as `realPhaseCExp`, while the
simulated experiment is `simPhaseCExp`, which additionally exposes the bad
branch where the simulator attempts to program a pre-existing target point.

The phase decomposes into six small sublemmas plus two thin compositions:

* **C1 `adv_advantage_eq_freshSuccess_realPhaseCExp`** — the CMA advantage
  is exactly the `freshSuccess` mass of `realPhaseCExp`. Pure repackaging of
  `unforgeableExp` through `(runtime M).evalDist`.
* **C2 `probEvent_badOrFreshSuccess_realPhaseCExp_le`** — the HVZK hybrid:
  `Pr[badOrFreshSuccess | realPhaseCExp] ≤ Pr[badOrFreshSuccess | simPhaseCExp]
  + qS · ζ_zk`. Per-query identical-until-bad coupling charged against
  `signHashQueryBound`.
* **C3 `probEvent_freshSuccess_le_badOrFreshSuccess`** — pointwise event
  monotonicity, `freshSuccess ⇒ badOrFreshSuccess`.
* **C5 `probEvent_badOrFreshSuccess_le_bad_add_fresh`** — union split,
  `Pr[bad ∨ freshSuccess] ≤ Pr[bad] + Pr[freshSuccess]`.
* **C6 `probEvent_bad_simPhaseCExp_le_collisionSlack`** — birthday bound
  against `simCommitPredictability`, summed across the `qS` signing queries.
* **C7 `probEvent_freshSuccess_simPhaseCExp_le_managedRoAdvantage`** —
  state-projection alignment between `simPhaseCExp` and
  `managedRoNmaExp (nmaAdvFromHVZK)`; on the `!wasSigned` event the extra
  `signLog`/`bad` bookkeeping aligns the cache-projected hash distributions and
  monotonicity drops the freshness filter to expose the unconditioned `verified`
  marginal of the managed-RO experiment.

`phaseC_real_le_sim_bad_or_fresh` and
`phaseC_sim_bad_or_fresh_le_managedRo_plus_collision` are then thin `calc`
compositions consumed by `hybrid_sign_le`.
-/

omit [Fintype Chal] in
/-- **C1.** The CMA-EUF advantage of `adv` equals the `freshSuccess` mass of
`realPhaseCExp`: `unforgeableExp` runs the same simulator-free signing path that
`realPhaseCExp` exposes, and its success bit `!log.wasQueried msg && verified`
matches `freshSuccess` after `phaseCResultOf`. -/
private lemma adv_advantage_eq_freshSuccess_realPhaseCExp :
    adv.advantage (runtime M) =
      Pr[= true | PhaseCResult.freshSuccess <$> realPhaseCExp σ hr M adv] := by
  sorry

omit [Fintype Chal] in
/-- **C2.** Phase C HVZK hybrid in the form ultimately consumed by
`phaseC_real_le_sim_bad_or_fresh`. The real and simulated Phase C experiments
agree pointwise outside the `bad` flag (per-query coupling), and inside the bad
branch the per-query gap is bounded by `tvDist (realTranscript) (simTranscript)
≤ ζ_zk`. Summed across at most `qS` signing queries this contributes
`qS · ζ_zk` of total-variation slack on `badOrFreshSuccess`. -/
private lemma probEvent_badOrFreshSuccess_realPhaseCExp_le
    (_hζ_zk : 0 ≤ ζ_zk) (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true | PhaseCResult.badOrFreshSuccess <$> realPhaseCExp σ hr M adv] ≤
      Pr[= true | PhaseCResult.badOrFreshSuccess <$>
          simPhaseCExp σ hr M simTranscript adv] +
        ENNReal.ofReal (qS * ζ_zk) := by
  sorry

omit [Fintype Chal] [SampleableType Chal] [SampleableType Stmt] [SampleableType Wit]
  [DecidableEq M] [DecidableEq Commit] in
/-- **C3.** Pointwise event monotonicity: `freshSuccess ⇒ badOrFreshSuccess`. -/
private lemma probEvent_freshSuccess_le_badOrFreshSuccess
    (m : SPMF PhaseCResult) :
    Pr[= true | PhaseCResult.freshSuccess <$> m] ≤
      Pr[= true | PhaseCResult.badOrFreshSuccess <$> m] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  refine probEvent_mono fun r _ hfresh => ?_
  simp only [Function.comp_apply, PhaseCResult.badOrFreshSuccess,
    PhaseCResult.freshSuccess, Bool.or_eq_true] at hfresh ⊢
  exact Or.inr hfresh

omit [Fintype Chal] [SampleableType Chal] [SampleableType Stmt] [SampleableType Wit]
  [DecidableEq M] [DecidableEq Commit] in
/-- **C5.** Union split of the `badOrFreshSuccess` event: the probability is at
most the sum of the `bad` and `freshSuccess` marginals. -/
private lemma probEvent_badOrFreshSuccess_le_bad_add_fresh
    (m : SPMF PhaseCResult) :
    Pr[= true | PhaseCResult.badOrFreshSuccess <$> m] ≤
      Pr[= true | (·.bad) <$> m] +
        Pr[= true | PhaseCResult.freshSuccess <$> m] := by
  have hLHS :
      Pr[= true | PhaseCResult.badOrFreshSuccess <$> m] =
        Pr[fun r : PhaseCResult => r.bad = true ∨ r.freshSuccess = true | m] := by
    rw [← probEvent_eq_eq_probOutput', probEvent_map]
    refine probEvent_ext fun r _ => ?_
    simp [Function.comp_apply, PhaseCResult.badOrFreshSuccess, Bool.or_eq_true]
  have hBad :
      Pr[= true | (·.bad) <$> m] = Pr[fun r : PhaseCResult => r.bad = true | m] := by
    rw [← probEvent_eq_eq_probOutput', probEvent_map]
    refine probEvent_ext fun r _ => ?_
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hFresh :
      Pr[= true | PhaseCResult.freshSuccess <$> m] =
        Pr[fun r : PhaseCResult => r.freshSuccess = true | m] := by
    rw [← probEvent_eq_eq_probOutput', probEvent_map]
    refine probEvent_ext fun r _ => ?_
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hLHS, hBad, hFresh]
  exact probEvent_or_le m _ _

omit [Fintype Chal] in
/-- **C6.** The simulator's `bad` flag fires only when one of the (at most `qS`)
HVZK transcripts programs a `(msg, c)` point that already lives in the cache.
Per query the predictability hypothesis bounds the chance by `(qS + qH) · β`,
and the union bound across `qS` queries gives `collisionSlack qS qH β`. -/
private lemma probEvent_bad_simPhaseCExp_le_collisionSlack
    (β : ℝ≥0∞) (_hβ : SigmaProtocol.simCommitPredictability simTranscript β)
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true | (·.bad) <$> simPhaseCExp σ hr M simTranscript adv] ≤
      collisionSlack qS qH β := by
  sorry

/-!
**C7 sub-decomposition (corrected).**

Earlier the lemma `probEvent_verified_simPhaseCExp_le_managedRoAdvantage`
(unconditional `verified` marginal of `simPhaseCExp` bounded by the managed-RO
advantage) was wrongly proposed: on adversaries that re-output a signed message
as the forgery, `simPhaseCExp.verified` is `1` (programmed transcript verifies
deterministically) while `managedRoNmaExp.verified` is only `~1/|Chal|` (fresh
random-oracle sample at the verification query). Dropping the `!wasSigned`
filter therefore loses essential information.

The corrected decomposition keeps the freshness filter through the alignment
step:

* **C7-i `nmaAdvFromHVZK_advantage_eq_freshSuccess_managedRoExtended`** —
  define an "extended" managed-RO experiment that mirrors `simPhaseCExp` on
  `(wasSigned, verified)` for the projected state. On the `!wasSigned` branch
  `phaseCHashImpl` reduces to the `roSimImpl` cache lookup (by
  `phaseCOverlayInvariant.agreesAwayFromSigned`), so the joint `(wasSigned,
  verified)` distribution agrees with that of `nmaAdvFromHVZK`'s managed-RO
  trace augmented with a parallel `signLog`. This step does the heavy
  state-projection work via `relTriple_simulateQ_run_of_impl_eq_preservesInv`.
* **C7-ii `freshSuccess_managedRoExtended_le_verified_managedRo`** — drop the
  `!wasSigned` filter, monotonicity. The augmented experiment's `verified`
  marginal equals the unaugmented one.

`probEvent_freshSuccess_simPhaseCExp_le_managedRoAdvantage` then composes the
two, replacing the old C7a/C7b chain. -/

/-! #### C7 sub-lemma: extended managed-RO experiment with sign log -/

/-- Extended state for the managed-RO experiment that additionally tracks the sign log.
The `cache` field corresponds to the standard `QueryCache`, while `extSignLog` records
which messages were signed, enabling the `!wasSigned` freshness filter. -/
private structure ManagedRoExtState where
  cache : PhaseCCache (M := M) (Commit := Commit) (Chal := Chal)
  extSignLog : PhaseCSignLog (M := M) (Commit := Commit) (Resp := Resp)

/-- Uniform-spec forwarder lifted to the extended managed-RO state: forwards uniform
queries to the outer oracle without touching the state (mirroring `unifSimImpl`). -/
private def unifSimImplExt :
    QueryImpl unifSpec
      (StateT (ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun n => liftM (query (spec := PhaseCOuterSpec) (.inl n))

/-- Caching RO simulator lifted to the extended managed-RO state: checks `cache`,
on miss forwards to the outer oracle and caches the result (mirroring `roSimImpl`). -/
private noncomputable def roSimImplExt :
    QueryImpl (M × Commit →ₒ Chal)
      (StateT (ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun mc => do
    let st ← get
    match st.cache (.inr mc) with
    | some v => pure v
    | none =>
        let v ← liftM (query (spec := PhaseCOuterSpec) (.inr mc))
        set ({ st with cache := st.cache.cacheQuery (.inr mc) v } :
          ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        pure v

/-- Base simulator lifted to the extended state. -/
private noncomputable def baseSimImplExt :
    QueryImpl PhaseCOuterSpec
      (StateT (ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  unifSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
    roSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)

/-- Extended signing simulator: like `sigSimImpl` but additionally logs the signed
message in `extSignLog`. -/
private noncomputable def sigSimImplExt
    (pk : Stmt) :
    QueryImpl (M →ₒ (Commit × Resp))
      (StateT (ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (OracleComp PhaseCOuterSpec)) :=
  fun msg => do
    let (c, ω, s) ← simulateQ
      (unifSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (simTranscript pk)
    modify fun st =>
      ({ cache := st.cache.cacheQuery (.inr (msg, c)) ω
         extSignLog := st.extSignLog.logQuery msg (c, s) } :
        ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
    pure (c, s)

/-- Extended managed-RO experiment: runs the CMA adversary with the HVZK signing simulator
that additionally tracks a sign log, then verifies against the live outer oracle. -/
private noncomputable def managedRoNmaExpExt : SPMF (Bool × Bool) :=
  (runtime M).evalDist do
    let sigAlg : SignatureAlg (OracleComp PhaseCOuterSpec) M Stmt Wit (Commit × Resp) :=
      FiatShamir (m := OracleComp PhaseCOuterSpec) σ hr M
    let (pk, _) ← sigAlg.keygen
    let extImpl : QueryImpl PhaseCFullSpec
        (StateT (ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
          (OracleComp PhaseCOuterSpec)) :=
      baseSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
        sigSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          simTranscript pk
    let initSt : ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) :=
      ⟨∅, []⟩
    let ((msg, sig), st) ← (simulateQ extImpl (adv.main pk)).run initSt
    let verified ← sigAlg.verify pk msg sig
    let wasSigned :=
      (letI : DecidableEq (Commit × Resp) := Classical.decEq _
       st.extSignLog.wasQueried msg)
    pure (wasSigned, verified)

omit [Fintype Chal] in
/-- **C7a.** The `freshSuccess` probability of `simPhaseCExp` is at most the
`!wasSigned && verified` probability in the extended managed-RO experiment.

The core state-projection step: under `phaseCOverlayInvariant`, the hash
behaviour of `phaseCHashImpl` agrees with `roSimImpl` via the projection
`st ↦ st.overlayCache`. The signing simulators agree on `(c, s)` output
and both record `(msg, c) ↦ ω`. For unsigned messages, verification through
`phaseCBaseImpl` reduces to the same outer-oracle lookup as direct verification.

The proof should proceed by:
1. Defining the state relation `R st extSt` connecting `PhaseCState` to
   `ManagedRoExtState` (overlayCache = cache, signLog = extSignLog, invariant holds)
2. Showing each query implementation preserves `R` and produces the same output
3. Applying `relTriple_simulateQ_run` (or a direct induction) to transport
   the output equality through the full simulation
4. Showing verification agrees on the `!wasSigned` branch -/
private lemma probEvent_freshSuccess_simPhaseCExp_le_ext :
    Pr[= true |
        PhaseCResult.freshSuccess <$> simPhaseCExp σ hr M simTranscript adv] ≤
      Pr[= true |
        (fun p : Bool × Bool => !p.1 && p.2) <$>
          managedRoNmaExpExt σ hr M simTranscript adv] := by
  sorry

omit [Fintype Chal] [SampleableType Stmt] [SampleableType Chal] in
private lemma extImpl_proj_eq (pk : Stmt)
    (t : (PhaseCOuterSpec + (M →ₒ (Commit × Resp))).Domain)
    (s : ManagedRoExtState (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) :
    Prod.map id ManagedRoExtState.cache <$>
      ((baseSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
        sigSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          simTranscript pk) t).run s =
      ((baseSimImpl (M := M) (Commit := Commit) (Chal := Chal) +
        sigSimImpl (M := M) simTranscript pk) t).run s.cache := by
  match t with
  | .inl (.inl n) =>
    simp only [QueryImpl.add_apply_inl, baseSimImplExt, baseSimImpl]
    simp [unifSimImplExt, unifSimImpl, fwdImpl, QueryImpl.liftTarget,
      Functor.map_map, Prod.map_apply]
  | .inl (.inr mc) =>
    simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      baseSimImplExt, baseSimImpl]
    change Prod.map id ManagedRoExtState.cache <$> (roSimImplExt M mc).run s =
      (roSimImpl M mc).run s.cache
    simp only [roSimImplExt, roSimImpl, fwdImpl, StateT.run_bind, StateT.run_get,
      pure_bind]
    split
    · simp [StateT.run_pure, Prod.map_apply]
    · simp [StateT.run_bind, StateT.run_set,
        StateT.run_modifyGet, QueryImpl.liftTarget, map_pure,
        Functor.map_map, Prod.map]
  | .inr msg =>
    simp only [QueryImpl.add_apply_inr]
    change Prod.map id ManagedRoExtState.cache <$> (sigSimImplExt M simTranscript pk msg).run s =
      (sigSimImpl M simTranscript pk msg).run s.cache
    simp only [sigSimImplExt, sigSimImpl, StateT.run_bind, map_bind,
      StateT.run_modify, StateT.run_pure, map_pure, StateT.run_modifyGet, pure_bind]
    have hinner := OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
      (unifSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (unifSimImpl (M := M) (Commit := Commit) (Chal := Chal))
      ManagedRoExtState.cache
      (by intro n st
          simp [unifSimImplExt, unifSimImpl, fwdImpl, QueryImpl.liftTarget,
            Functor.map_map, Prod.map_apply])
      (simTranscript pk) s
    rw [← hinner, seq_bind_eq, Function.comp_def]
    simp [Prod.map_apply, Prod.map_fst, Prod.map_snd, id_eq]

omit [Fintype Chal] [SampleableType Wit] [SampleableType Stmt] in
/-- **C7b.** The `!wasSigned && verified` probability in the extended managed-RO
experiment is at most the `verified` probability in the standard `managedRoNmaExp`.

This is the composition of two observations:
1. Event monotonicity: `!wasSigned && verified → verified`
2. State erasure: dropping the sign log from `ManagedRoExtState` does not
   affect the `verified` distribution (by `run'_simulateQ_eq_of_query_map_eq'`
   with projection `st ↦ st.cache`). -/
private lemma probEvent_ext_le_managedRoAdvantage :
    Pr[= true |
        (fun p : Bool × Bool => !p.1 && p.2) <$>
          managedRoNmaExpExt σ hr M simTranscript adv] ≤
      SignatureAlg.managedRoNmaAdv.advantage (runtime M)
        (nmaAdvFromHVZK σ hr M simTranscript adv) := by
  calc Pr[= true | (fun p ↦ !p.1 && p.2) <$> managedRoNmaExpExt σ hr M simTranscript adv]
      ≤ Pr[= true | Prod.snd <$> managedRoNmaExpExt σ hr M simTranscript adv] := by
          rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
              probEvent_map, probEvent_map]
          exact probEvent_mono
            (fun p _ hp => by
              simp only [Function.comp, Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
              exact hp.2)
    _ = SignatureAlg.managedRoNmaAdv.advantage (runtime M)
          (nmaAdvFromHVZK σ hr M simTranscript adv) := by
        simp only [SignatureAlg.managedRoNmaAdv.advantage, SignatureAlg.managedRoNmaExp,
          managedRoNmaExpExt, nmaAdvFromHVZK]
        congr 1
        rw [← runtime_evalDist_map]
        congr 1
        simp only [map_bind, map_pure]
        congr 1 with ⟨pk, sk⟩
        simp only [bind_pure]
        have key : ∀ (σ' : Type)
            (mx : OracleComp PhaseCOuterSpec ((M × (Commit × Resp)) × σ')),
            (mx >>= fun a => (FiatShamir σ hr M).verify pk a.1.1 a.1.2) =
            ((Prod.fst <$> mx) >>= fun ms =>
              (FiatShamir σ hr M).verify pk ms.1 ms.2) := by
          intro σ' mx
          rw [show (fun a : (M × (Commit × Resp)) × σ' =>
                (FiatShamir σ hr M).verify pk a.1.1 a.1.2) =
              ((fun ms => (FiatShamir σ hr M).verify pk ms.1 ms.2) ∘ Prod.fst)
            from rfl]
          rw [← seq_bind_eq]
        rw [key, key, ← StateT.run'_eq, ← StateT.run'_eq]
        congr 1
        exact OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq'
          (baseSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) +
            sigSimImplExt (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
              simTranscript pk)
          (baseSimImpl (M := M) (Commit := Commit) (Chal := Chal) +
            sigSimImpl (M := M) simTranscript pk)
          ManagedRoExtState.cache
          (fun t s => extImpl_proj_eq M simTranscript pk t s)
          (adv.main pk) _

omit [Fintype Chal] in
/-- **C7.** State-projection alignment between `simPhaseCExp` and
`managedRoNmaExp (nmaAdvFromHVZK)` on the `freshSuccess = !wasSigned ∧ verified`
event. Composes C7a (state-projection) and C7b (event monotonicity + state erasure). -/
private lemma probEvent_freshSuccess_simPhaseCExp_le_managedRoAdvantage :
    Pr[= true |
        PhaseCResult.freshSuccess <$> simPhaseCExp σ hr M simTranscript adv] ≤
      SignatureAlg.managedRoNmaAdv.advantage (runtime M)
        (nmaAdvFromHVZK σ hr M simTranscript adv) :=
  le_trans
    (probEvent_freshSuccess_simPhaseCExp_le_ext σ hr M simTranscript adv)
    (probEvent_ext_le_managedRoAdvantage σ hr M simTranscript adv)

omit [Fintype Chal] in
/-- **C4.** Phase C hybrid step (composition of C1, C3, C2): the EUF-CMA
advantage is bounded by the simulated `badOrFreshSuccess` event, plus the HVZK
loss `qS · ζ_zk`. -/
lemma phaseC_real_le_sim_bad_or_fresh
    (_hζ_zk : 0 ≤ ζ_zk) (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    adv.advantage (runtime M) ≤
      Pr[= true | PhaseCResult.badOrFreshSuccess <$>
        (simPhaseCExp σ hr M simTranscript adv)] +
        ENNReal.ofReal (qS * ζ_zk) := by
  calc adv.advantage (runtime M)
      = Pr[= true | PhaseCResult.freshSuccess <$> realPhaseCExp σ hr M adv] :=
        adv_advantage_eq_freshSuccess_realPhaseCExp σ hr M adv
    _ ≤ Pr[= true | PhaseCResult.badOrFreshSuccess <$> realPhaseCExp σ hr M adv] :=
        probEvent_freshSuccess_le_badOrFreshSuccess _
    _ ≤ Pr[= true | PhaseCResult.badOrFreshSuccess <$>
            simPhaseCExp σ hr M simTranscript adv] +
          ENNReal.ofReal (qS * ζ_zk) :=
        probEvent_badOrFreshSuccess_realPhaseCExp_le σ hr M simTranscript ζ_zk adv
          _hζ_zk _hhvzk qS qH _hQ

omit [Fintype Chal] in
/-- **C8.** Phase C bad-event bridge (composition of C5, C6, C7): the
simulator's `bad ∨ freshSuccess` event is bounded by the live managed-RO
experiment plus the collision slack. -/
lemma phaseC_sim_bad_or_fresh_le_managedRo_plus_collision
    (β : ℝ≥0∞) (_hβ : SigmaProtocol.simCommitPredictability simTranscript β)
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true | PhaseCResult.badOrFreshSuccess <$>
      (simPhaseCExp σ hr M simTranscript adv)] ≤
      SignatureAlg.managedRoNmaAdv.advantage (runtime M)
          (nmaAdvFromHVZK σ hr M simTranscript adv) +
        collisionSlack qS qH β := by
  calc Pr[= true | PhaseCResult.badOrFreshSuccess <$>
            simPhaseCExp σ hr M simTranscript adv]
      ≤ Pr[= true | (·.bad) <$> simPhaseCExp σ hr M simTranscript adv] +
          Pr[= true | PhaseCResult.freshSuccess <$>
            simPhaseCExp σ hr M simTranscript adv] :=
        probEvent_badOrFreshSuccess_le_bad_add_fresh _
    _ ≤ collisionSlack qS qH β +
          SignatureAlg.managedRoNmaAdv.advantage (runtime M)
            (nmaAdvFromHVZK σ hr M simTranscript adv) :=
        add_le_add
          (probEvent_bad_simPhaseCExp_le_collisionSlack σ hr M simTranscript adv
            β _hβ qS qH _hQ)
          (probEvent_freshSuccess_simPhaseCExp_le_managedRoAdvantage σ hr M
            simTranscript adv)
    _ = SignatureAlg.managedRoNmaAdv.advantage (runtime M)
          (nmaAdvFromHVZK σ hr M simTranscript adv) + collisionSlack qS qH β := by
        rw [add_comm]

omit [Fintype Chal] in
/-- **Phase C (freshness-aware hybrid + live bridge).**
The EUF-CMA success probability is bounded by the canonical live managed-RO NMA
experiment for `nmaAdvFromHVZK`, plus the HVZK loss `qS · ζ_zk` and the
late-programming slack `collisionSlack qS qH β`. -/
lemma hybrid_sign_le
    (β : ℝ≥0∞) (_hβ : SigmaProtocol.simCommitPredictability simTranscript β)
    (_hζ_zk : 0 ≤ ζ_zk) (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    adv.advantage (runtime M) ≤
      SignatureAlg.managedRoNmaAdv.advantage (runtime M)
          (nmaAdvFromHVZK σ hr M simTranscript adv) +
        ENNReal.ofReal (qS * ζ_zk) +
        collisionSlack qS qH β := by
  calc adv.advantage (runtime M)
      ≤ Pr[= true | PhaseCResult.badOrFreshSuccess <$>
            (simPhaseCExp σ hr M simTranscript adv)] +
          ENNReal.ofReal (qS * ζ_zk) :=
        phaseC_real_le_sim_bad_or_fresh σ hr M simTranscript ζ_zk adv
          _hζ_zk _hhvzk qS qH _hQ
    _ ≤ (SignatureAlg.managedRoNmaAdv.advantage (runtime M)
            (nmaAdvFromHVZK σ hr M simTranscript adv) +
          collisionSlack qS qH β) +
          ENNReal.ofReal (qS * ζ_zk) := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (phaseC_sim_bad_or_fresh_le_managedRo_plus_collision σ hr M simTranscript adv
              β _hβ qS qH _hQ)
            (ENNReal.ofReal (qS * ζ_zk))
    _ = SignatureAlg.managedRoNmaAdv.advantage (runtime M)
          (nmaAdvFromHVZK σ hr M simTranscript adv) +
        ENNReal.ofReal (qS * ζ_zk) + collisionSlack qS qH β := by
        simp [add_comm, add_left_comm, mul_comm]

omit [Fintype Chal] [SampleableType Chal] in
private def wrappedHashQueryBound {α : Type}
    (oa : OracleComp (Fork.wrappedSpec Chal) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl _ => True
      | .inr _ => 0 < b)
    (fun t b => match t with
      | .inl _ => b
      | .inr _ => b - 1)

omit [Fintype Chal] [SampleableType Chal] in
@[simp] private lemma wrappedHashQueryBound_query_bind_iff {α : Type}
    (t : (Fork.wrappedSpec Chal).Domain)
    (oa : (Fork.wrappedSpec Chal).Range t → OracleComp (Fork.wrappedSpec Chal) α)
    (Q : ℕ) :
    wrappedHashQueryBound (Chal := Chal)
      (oa := liftM (query (spec := Fork.wrappedSpec Chal) t) >>= oa) Q ↔
      (match t with
      | .inl _ => True
      | .inr _ => 0 < Q) ∧
      ∀ u,
        wrappedHashQueryBound (Chal := Chal)
          (oa := oa u) (match t with
            | .inl _ => Q
            | .inr _ => Q - 1) := by
  cases t with
  | inl n =>
      simpa [wrappedHashQueryBound] using
        (OracleComp.isQueryBound_query_bind_iff
          (spec := Fork.wrappedSpec Chal)
          (α := α) (t := Sum.inl n) (mx := oa) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))
  | inr u =>
      simpa [wrappedHashQueryBound] using
        (OracleComp.isQueryBound_query_bind_iff
          (spec := Fork.wrappedSpec Chal)
          (α := α) (t := Sum.inr u) (mx := oa) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))

omit [Fintype Chal] [SampleableType Chal] in
@[simp] private lemma wrappedHashQueryBound_query_iff
    (t : (Fork.wrappedSpec Chal).Domain) (Q : ℕ) :
    wrappedHashQueryBound (Chal := Chal)
      (oa := liftM (query (spec := Fork.wrappedSpec Chal) t)) Q ↔
      match t with
      | .inl _ => True
      | .inr _ => 0 < Q := by
  cases t with
  | inl n =>
      simpa [wrappedHashQueryBound] using
        (OracleComp.isQueryBound_query_iff
          (spec := Fork.wrappedSpec Chal)
          (t := Sum.inl n) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))
  | inr u =>
      simpa [wrappedHashQueryBound] using
        (OracleComp.isQueryBound_query_iff
          (spec := Fork.wrappedSpec Chal)
          (t := Sum.inr u) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))

omit [Fintype Chal] [SampleableType Chal] in
private lemma wrappedHashQueryBound_mono {α : Type}
    {oa : OracleComp (Fork.wrappedSpec Chal) α} {Q₁ Q₂ : ℕ}
    (h : wrappedHashQueryBound (Chal := Chal) (oa := oa) Q₁)
    (hQ : Q₁ ≤ Q₂) :
    wrappedHashQueryBound (Chal := Chal) (oa := oa) Q₂ := by
  induction oa using OracleComp.inductionOn generalizing Q₁ Q₂ with
  | pure _ =>
      simp [wrappedHashQueryBound]
  | query_bind t mx ih =>
      rw [wrappedHashQueryBound_query_bind_iff] at h ⊢
      cases t with
      | inl n =>
          refine ⟨trivial, fun u => ?_⟩
          exact ih (u := u) (h := h.2 u) hQ
      | inr u =>
          refine ⟨Nat.lt_of_lt_of_le h.1 hQ, fun v => ?_⟩
          exact ih (u := v) (h := h.2 v) (Nat.sub_le_sub_right hQ 1)

omit [Fintype Chal] [SampleableType Chal] in
private lemma wrappedHashQueryBound_bind {α β : Type}
    {oa : OracleComp (Fork.wrappedSpec Chal) α}
    {ob : α → OracleComp (Fork.wrappedSpec Chal) β}
    {Q₁ Q₂ : ℕ}
    (h1 : wrappedHashQueryBound (Chal := Chal) (oa := oa) Q₁)
    (h2 : ∀ x, wrappedHashQueryBound (Chal := Chal) (oa := ob x) Q₂) :
    wrappedHashQueryBound (Chal := Chal)
      (oa := oa >>= ob) (Q₁ + Q₂) := by
  induction oa using OracleComp.inductionOn generalizing Q₁ with
  | pure x =>
      simpa [pure_bind] using
        wrappedHashQueryBound_mono (Chal := Chal) (h2 x) (Nat.le_add_left _ _)
  | query_bind t mx ih =>
      rw [wrappedHashQueryBound_query_bind_iff] at h1
      rw [bind_assoc, wrappedHashQueryBound_query_bind_iff]
      cases t with
      | inl n =>
          refine ⟨trivial, fun u => ?_⟩
          simpa using ih u (h1.2 u)
      | inr u =>
          refine ⟨Nat.add_pos_left h1.1 _, fun v => ?_⟩
          have h3 := ih v (h1.2 v)
          have hEq : (Q₁ - 1) + Q₂ = Q₁ + Q₂ - 1 := by omega
          simpa [hEq] using h3

private theorem log_count_le_of_isQueryBound
    {ι : Type} {spec : OracleSpec ι} {α : Type}
    (counted : spec.Domain → Prop) [DecidablePred counted]
    {oa : OracleComp spec α} {Q : ℕ}
    (hQ : OracleComp.IsQueryBound oa Q
      (fun t b => if counted t then 0 < b else True)
      (fun t b => if counted t then b - 1 else b))
    {z : α × QueryLog spec}
    (hz : z ∈ support ((simulateQ (loggingOracle (spec := spec)) oa).run)) :
    z.2.countQ counted ≤ Q := by
  induction oa using OracleComp.inductionOn generalizing Q z with
  | pure x =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [QueryLog.countQ]
  | query_bind t mx ih =>
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind] at hz
      rw [OracleComp.isQueryBound_query_bind_iff] at hQ
      rw [support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨u, _, z', hz', rfl⟩ := hz
      by_cases ht : counted t
      · have hrest : z'.2.countQ counted ≤ Q - 1 :=
          ih (u := u) (Q := Q - 1)
            (hQ := by simpa [ht] using hQ.2 u) hz'
        have hpos : 0 < Q := by simpa [ht] using hQ.1
        simp [QueryLog.countQ, QueryLog.getQ_cons, ht] at hrest ⊢
        omega
      · have hrest : z'.2.countQ counted ≤ Q :=
          ih (u := u) (Q := Q) (hQ := by simpa [ht] using hQ.2 u) hz'
        simpa [QueryLog.countQ, QueryLog.getQ_cons, ht] using hrest

-- Section instances are needed in proofs; `omit` breaks TC. Flexible `simp` is required for `hus'`.
set_option linter.unusedSectionVars false in
set_option linter.flexible false in
omit [Fintype Chal] in
private theorem runTraceImpl_cache_entry_or_mem
    {γ : Type}
    (Y : OracleComp (unifSpec + (M × Commit →ₒ Chal)) γ)
    (cache₀ : (M × Commit →ₒ Chal).QueryCache) (log₀ : List (M × Commit))
    {z : γ × Fork.simSt M Commit Chal}
    (hz : z ∈ support
      ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) Y).run
        (cache₀, log₀))) :
    (∃ logNew, z.2.2 = log₀ ++ logNew) ∧
    (∀ mc ω, z.2.1 mc = some ω → cache₀ mc = some ω ∨ mc ∈ z.2.2) := by
  induction Y using OracleComp.inductionOn generalizing cache₀ log₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨⟨[], by simp⟩, ?_⟩
      intro mc ω hmc
      exact Or.inl hmc
  | query_bind t Y ih =>
      have hrun :
          (simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
            ((liftM (query t) : OracleComp _ _) >>= Y)).run (cache₀, log₀) =
            (((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) t).run (cache₀, log₀)) >>=
              fun us =>
                (simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                  (Y us.1)).run us.2 := by
        simp [simulateQ_bind, simulateQ_query, StateT.run_bind,
          OracleQuery.input_query, OracleQuery.cont_query, map_eq_bind_pure_comp]
      rw [hrun, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hrest⟩ := hz
      rcases us with ⟨u, st⟩
      rcases st with ⟨cacheMid, logMid⟩
      cases t with
      | inl n =>
          have hus' : (u, (cacheMid, logMid)) ∈
              support (((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) (.inl n)).run
                (cache₀, log₀)) := hus
          simp [Fork.unifFwd, QueryImpl.add_apply_inl] at hus'
          rcases hus' with ⟨u', hEq⟩
          cases hEq
          exact ih (u := u) (cache₀ := cache₀) (log₀ := log₀) hrest
      | inr mc =>
          have hus' : (u, (cacheMid, logMid)) ∈
              support (((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) (.inr mc)).run
                (cache₀, log₀)) := hus
          by_cases hcache : cache₀ mc = none
          · simp [Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
              StateT.run_set, hcache] at hus'
            rcases hus' with ⟨u', hEq⟩
            cases hEq
            rcases ih (u := u) (cache₀ := cache₀.cacheQuery mc u) (log₀ := log₀ ++ [mc]) hrest with
              ⟨⟨logNew, hlog⟩, hmem⟩
            refine ⟨⟨mc :: logNew, ?_⟩, ?_⟩
            · rw [hlog]
              simp [List.append_assoc]
            · intro mc' ω hmc'
              have hmem' := hmem mc' ω hmc'
              rcases hmem' with hOld | hIn
              · by_cases hEq : mc' = mc
                · subst hEq
                  right
                  rw [hlog]
                  simp
                · left
                  rw [QueryCache.cacheQuery_of_ne _ _ hEq] at hOld
                  exact hOld
              · right
                rw [hlog] at hIn ⊢
                exact hIn
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            simp [Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
              hv.symm] at hus'
            cases hus'
            exact ih (u := u) (cache₀ := cache₀) (log₀ := log₀) hrest

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private theorem runTrace_target_mem_queryLog
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt)
    {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog : QueryLog (Fork.wrappedSpec Chal)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    x.target ∈ x.queryLog := by
  classical
  unfold replayFirstRun Fork.runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  rcases a with ⟨a, log_a⟩
  rcases a with ⟨a, st⟩
  rcases a with ⟨a, ω⟩
  rcases a with ⟨forgery, advCache⟩
  rcases st with ⟨roCache, queryLog⟩
  have hxeq : x =
      ({ forgery := forgery,
         advCache := advCache,
         roCache := roCache,
         queryLog := queryLog,
         verified := σ.verify pk forgery.2.1 ω forgery.2.2 } :
        Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := by
    have := congrArg Prod.fst ha_eq
    simpa using this.symm
  rw [hxeq]
  simp only [Fork.Trace.target]
  have hinner :
      (((forgery, advCache), ω), (roCache, queryLog)) ∈
        support
          ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) (do
              let result@(forgery, _) ← nmaAdv.main pk
              match forgery with
              | (msg, (c, _)) =>
                  let ω ← query (spec := unifSpec + (M × Commit →ₒ Chal)) (.inr (msg, c))
                  pure (result, ω))).run (∅, [])) := by
    let oa :
        OracleComp (Fork.wrappedSpec Chal)
          ((((M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache) × Chal) ×
            Fork.simSt M Commit Chal) :=
      ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) (do
          let result@(forgery, _) ← nmaAdv.main pk
          match forgery with
          | (msg, (c, _)) =>
              let ω ← query (spec := unifSpec + (M × Commit →ₒ Chal)) (.inr (msg, c))
              pure (result, ω))).run (∅, []))
    have hfst :
        (((forgery, advCache), ω), (roCache, queryLog)) ∈
          support
            (Prod.fst <$> (simulateQ (loggingOracle (spec := Fork.wrappedSpec Chal)) oa).run) := by
      rw [support_map]
      exact ⟨((((forgery, advCache), ω), (roCache, queryLog)), log_a), ha_mem, rfl⟩
    rw [loggingOracle.fst_map_run_simulateQ] at hfst
    simpa [oa] using hfst
  simp only [simulateQ_bind, StateT.run_bind] at hinner
  rw [mem_support_bind_iff] at hinner
  obtain ⟨z, hz, hzω⟩ := hinner
  rcases z with ⟨res, st⟩
  rcases res with ⟨forgery', advCache'⟩
  rcases st with ⟨cache, log⟩
  rw [mem_support_bind_iff] at hzω
  obtain ⟨ω', hω', hfinal⟩ := hzω
  rcases ω' with ⟨ω', st'⟩
  rcases st' with ⟨cache', log'⟩
  have hfinal_eq :
      (((forgery, advCache), ω), (roCache, queryLog)) =
        (((forgery', advCache'), ω'), (cache', log')) := by
    simpa [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hfinal
  have hfg : forgery = forgery' := by
    have := congrArg (fun p => p.1.1.1) hfinal_eq
    simpa using this
  have hadv : advCache = advCache' := by
    have := congrArg (fun p => p.1.1.2) hfinal_eq
    simpa using this
  have hωeq : ω = ω' := by
    have := congrArg (fun p => p.1.2) hfinal_eq
    simpa using this
  have hcacheEq : roCache = cache' := by
    have := congrArg (fun p => p.2.1) hfinal_eq
    simpa using this
  have hlogEq : queryLog = log' := by
    have := congrArg (fun p => p.2.2) hfinal_eq
    simpa using this
  subst hfg hadv hωeq hcacheEq hlogEq
  have hstep :
      (ω, (roCache, queryLog)) ∈
        support ((Fork.roImpl M Commit Chal (forgery.1, forgery.2.1)).run (cache, log)) := by
    simpa [simulateQ_query, QueryImpl.add_apply_inr] using hω'
  by_cases hcache : cache (forgery.1, forgery.2.1) = none
  · simp only [Fork.roImpl, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hcache,
      StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set, map_pure,
      Functor.map_map, support_map, support_liftM, OracleQuery.input_query, add_apply_inr,
      OracleQuery.cont_query, Set.range_id, Set.image_univ, Set.mem_range, Prod.mk.injEq,
      exists_eq_left] at hstep
    rcases hstep with ⟨_hro, hlog⟩
    rw [← hlog]
    simp
  · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
    have hhit : (ω, roCache, queryLog) = (v, cache, log) := by
      simpa [Fork.roImpl, StateT.run_bind, StateT.run_get, hv.symm, support_pure,
        Set.mem_singleton_iff] using hstep
    cases hhit
    have hmem_or :=
      (runTraceImpl_cache_entry_or_mem (M := M) (Commit := Commit) (Chal := Chal)
        (Y := nmaAdv.main pk) ∅ [] hz).2 (forgery.1, forgery.2.1) ω (by simpa using hv.symm)
    rcases hmem_or with hinit | hmem
    · simp at hinit
    · simpa using hmem

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private lemma runTraceImpl_step_wrappedHashQueryBound
    [SampleableType Chal]
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain) (b : ℕ) (s : Fork.simSt M Commit Chal)
    (ht : match t with
      | .inl _ => True
      | .inr _ => 0 < b) :
    wrappedHashQueryBound (Chal := Chal)
      (oa := (((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) t).run s))
      (match t with
        | .inl _ => 0
        | .inr _ => 1) := by
  cases t with
  | inl n =>
      simpa [Fork.unifFwd, QueryImpl.add_apply_inl] using
        (wrappedHashQueryBound_query_iff (Chal := Chal) (t := Sum.inl n) (Q := 0))
  | inr mc =>
      rcases s with ⟨cache, log⟩
      by_cases hcache : cache mc = none
      · simpa [Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, hcache,
          wrappedHashQueryBound, OracleComp.isQueryBound_map_iff] using
          (wrappedHashQueryBound_query_iff (Chal := Chal) (t := Sum.inr ()) (Q := 1))
      · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
        simp [Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, hv.symm,
          wrappedHashQueryBound]

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private theorem runTrace_queryLog_length_le
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (hBound : ∀ pk,
      nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := nmaAdv.main pk) qH)
    (pk : Stmt)
    {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog : QueryLog (Fork.wrappedSpec Chal)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    x.queryLog.length ≤ qH + 1 := by
  have hlen : x.queryLog.length = outerLog.countQ (· = Sum.inr ()) :=
    Fork.runTrace_queryLog_length_eq σ hr M nmaAdv pk hx
  rw [hlen]
  unfold replayFirstRun Fork.runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hlog_eq : a.2 = outerLog := by
    have := congrArg Prod.snd ha_eq
    simpa [Prod.map_apply] using this
  rw [← hlog_eq]
  let wrappedMain :
      OracleComp (unifSpec + (M × Commit →ₒ Chal))
        (((M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache) × Chal) := do
    let result@(forgery, _) ← nmaAdv.main pk
    match forgery with
    | (msg, (c, _)) =>
        let ω ← query (spec := unifSpec + (M × Commit →ₒ Chal)) (.inr (msg, c))
        pure (result, ω)
  let oa :
      OracleComp (Fork.wrappedSpec Chal)
        ((((M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache) × Chal) ×
          Fork.simSt M Commit Chal) :=
    ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) wrappedMain).run
      (∅, []))
  have hwrapped :
      nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := wrappedMain)
        (qH + 1) := by
    refine FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
      (Q₁ := qH) (Q₂ := 1) (hBound pk) ?_
    intro result
    rcases result with ⟨forgery, advCache⟩
    rcases forgery with ⟨msg, c, resp⟩
    simpa [FiatShamir.nmaHashQueryBound, OracleComp.isQueryBound_map_iff] using
      (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
        (t := Sum.inr (msg, c)) (Q := 1))
  have hoa :
      OracleComp.IsQueryBound oa (qH + 1)
        (fun t b => match t with
          | .inl _ => True
          | .inr _ => 0 < b)
        (fun t b => match t with
          | .inl _ => b
          | .inr _ => b - 1) := by
    refine OracleComp.IsQueryBound.simulateQ_run_of_step
      (spec := unifSpec + (M × Commit →ₒ Chal))
      (spec' := Fork.wrappedSpec Chal)
      (impl := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
      (canQuery := fun t b => match t with
        | .inl _ => True
        | .inr _ => 0 < b)
      (cost := fun t b => match t with
        | .inl _ => b
        | .inr _ => b - 1)
      (canQuery' := fun t b => match t with
        | .inl _ => True
        | .inr _ => 0 < b)
      (cost' := fun t b => match t with
        | .inl _ => b
        | .inr _ => b - 1)
      (combine := Nat.add)
      (mapBudget := id)
      (stepBudget := fun t b => match t with
        | .inl _ => 0
        | .inr _ => 1)
      (h := hwrapped)
      (hbind := by
        intro γ δ oa' ob b₁ b₂ h1 h2
        simpa [wrappedHashQueryBound] using
          wrappedHashQueryBound_bind (Chal := Chal)
            (by simpa [wrappedHashQueryBound] using h1)
            (fun x => by simpa [wrappedHashQueryBound] using h2 x))
      (hstep := by
        intro t b s ht
        cases t with
        | inl n =>
            simpa [wrappedHashQueryBound, Fork.unifFwd, QueryImpl.add_apply_inl] using
              (wrappedHashQueryBound_query_iff (Chal := Chal) (t := Sum.inl n) (Q := 0))
        | inr mc =>
            rcases s with ⟨cache, log⟩
            by_cases hcache : cache mc = none
            · simpa [wrappedHashQueryBound, Fork.roImpl, QueryImpl.add_apply_inr,
                StateT.run_bind, StateT.run_get, hcache, OracleComp.isQueryBound_map_iff] using
                (wrappedHashQueryBound_query_iff (Chal := Chal) (t := Sum.inr ()) (Q := 1))
            · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
              simp [Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, hv.symm])
      (hcombine := by
        intro t b ht
        cases t with
        | inl n => simp
        | inr mc =>
            have hpos : 0 < b := by simpa using ht
            simpa [Nat.add_comm] using (Nat.succ_pred_eq_of_pos hpos))
      (s := (∅, []))
  let counted : (Fork.wrappedSpec Chal).Domain → Prop := (· = Sum.inr ())
  letI : DecidablePred counted := by
    intro t
    classical
    infer_instance
  have hoaCounted :
      OracleComp.IsQueryBound oa (qH + 1)
        (fun t b => if counted t then 0 < b else True)
        (fun t b => if counted t then b - 1 else b) := by
    refine (OracleComp.isQueryBound_congr
      (oa := oa)
      (b := qH + 1)
      (canQuery₁ := fun t b => match t with
        | .inl _ => True
        | .inr _ => 0 < b)
      (canQuery₂ := fun t b => if counted t then 0 < b else True)
      (cost₁ := fun t b => match t with
        | .inl _ => b
        | .inr _ => b - 1)
      (cost₂ := fun t b => if counted t then b - 1 else b)
      (hcan := by
        intro t b
        cases t <;> simp [counted])
      (hcost := by
        intro t b
        cases t <;> simp [counted])).1 hoa
  have hcountA : a.2.countQ counted ≤ qH + 1 :=
    log_count_le_of_isQueryBound (oa := oa) (counted := counted) (hQ := hoaCounted) (hz := ha_mem)
  simpa [oa, counted] using hcountA

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private theorem runTrace_verified_imp_forkPoint
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (hBound : ∀ pk,
      nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := nmaAdv.main pk) qH)
    (pk : Stmt)
    {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {outerLog : QueryLog (Fork.wrappedSpec Chal)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk)))
    (hv : x.verified = true) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x).isSome =
        true := by
  classical
  have hmem : x.target ∈ x.queryLog :=
    runTrace_target_mem_queryLog (σ := σ) (hr := hr) (M := M) (Chal := Chal) nmaAdv pk hx
  have hlen : x.queryLog.length ≤ qH + 1 :=
    runTrace_queryLog_length_le (σ := σ) (hr := hr) (M := M) (Chal := Chal)
      nmaAdv qH hBound pk hx
  have hidxLen : x.queryLog.findIdx (· == x.target) < x.queryLog.length := by
    exact List.findIdx_lt_length_of_exists ⟨x.target, hmem, by simp⟩
  have hidx : x.queryLog.findIdx (· == x.target) < qH + 1 :=
    lt_of_lt_of_le hidxLen hlen
  simp [Fork.forkPoint, hv, hmem, hidx]

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private def runTraceImplNoLog
    [SampleableType Chal] :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) (OracleComp (Fork.wrappedSpec Chal)))
  | .inl n =>
      monadLift
        (query (spec := Fork.wrappedSpec Chal) (.inl n) :
          OracleComp (Fork.wrappedSpec Chal) ((Fork.wrappedSpec Chal).Range (.inl n)))
  | .inr mc => do
      match (← get) mc with
      | some ω => pure ω
      | none =>
          let ω ← monadLift
            (query (spec := Fork.wrappedSpec Chal) (.inr ()) :
              OracleComp (Fork.wrappedSpec Chal) ((Fork.wrappedSpec Chal).Range (.inr ())))
          modifyGet fun cache => (ω, cache.cacheQuery mc ω)

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private lemma runTraceImpl_proj_eq
    [SampleableType Chal]
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain)
    (s : Fork.simSt M Commit Chal) :
    Prod.map id Prod.fst <$>
        (((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) t).run s) =
      ((runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal) t).run s.1) := by
  rcases s with ⟨cache, log⟩
  cases t with
  | inl n =>
      simp [runTraceImplNoLog, Fork.unifFwd, QueryImpl.add_apply_inl]
  | inr mc =>
      by_cases hcache : cache mc = none
      · simp [runTraceImplNoLog, Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind,
          StateT.run_get, hcache, StateT.run_monadLift, monadLift_self, StateT.run_map,
          StateT.run_set]
      · rcases Option.ne_none_iff_exists.mp hcache with ⟨ω, hω⟩
        simp [runTraceImplNoLog, Fork.roImpl, QueryImpl.add_apply_inr, StateT.run_bind,
          StateT.run_get, hω.symm]

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private lemma support_simulateQ_unifChalImpl
    [SampleableType Chal]
    {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) :
    support (simulateQ (QueryImpl.id' unifSpec +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t mx ih =>
      rcases t with n | u
      · simp [simulateQ_bind, simulateQ_query, ih]
      · simp [simulateQ_bind, simulateQ_query, ih, uniformSampleImpl]

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private def runTraceProbImpl
    [SampleableType Chal] :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)
  | .inl n =>
      monadLift
        (query (spec := unifSpec) n : ProbComp ((unifSpec).Range n))
  | .inr mc => do
      match (← get) mc with
      | some ω => pure ω
      | none =>
          let ω ← $ᵗ Chal
          modifyGet fun cache => (ω, cache.cacheQuery mc ω)

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private lemma runTraceProbImpl_query_eq
    [SampleableType Chal]
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain)
    (cache : (M × Commit →ₒ Chal).QueryCache) :
    (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal) t).run cache =
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
        ((runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal) t).run cache) := by
  cases t with
  | inl n =>
      simp [runTraceProbImpl, runTraceImplNoLog]
  | inr mc =>
      by_cases hcache : cache mc = none
      · simp [runTraceProbImpl, runTraceImplNoLog, hcache, StateT.run_bind,
          StateT.run_get, StateT.run_monadLift, monadLift_self, uniformSampleImpl]
      · rcases Option.ne_none_iff_exists.mp hcache with ⟨ω, hω⟩
        simp [runTraceProbImpl, runTraceImplNoLog, hω.symm, StateT.run_bind, StateT.run_get]

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private lemma runTraceProbImpl_run_eq
    [SampleableType Chal]
    {α : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α)
    (cache : (M × Commit →ₒ Chal).QueryCache) :
    (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal)) oa).run cache =
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
        ((simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal)) oa).run
          cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      calc
        ((runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal) t).run cache >>=
            fun x =>
          (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
              (oa x.1)).run x.2)
            =
          (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
              ((runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal) t).run cache) >>=
                fun x =>
                simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                  ((simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                      (oa x.1)).run x.2)) := by
              rw [runTraceProbImpl_query_eq (M := M) (Commit := Commit) (Chal := Chal) t cache]
              refine bind_congr fun x => ?_
              simpa using ih x.1 x.2
        _ =
          simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
            (((runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal) t).run cache) >>=
              fun x =>
              (simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                  (oa x.1)).run x.2) := by
              rw [simulateQ_bind]
        _ = _ := by
              simp

set_option linter.unusedSectionVars false in
omit [Fintype Chal] in
private lemma runTraceProbImpl_run'_eq_runtime
    [SampleableType Chal]
    {α : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α)
    (cache : (M × Commit →ₒ Chal).QueryCache) :
    (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal)) oa).run' cache =
      StateT.run'
        (simulateQ (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) +
          (randomOracle (spec := (M × Commit →ₒ Chal)))) oa)
        cache := by
  refine OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq
    (impl₁ := runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
    (impl₂ := ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) +
      (randomOracle (spec := (M × Commit →ₒ Chal))))
    (proj := id) ?_ oa cache
  intro t s
  cases t with
  | inl n =>
      simp [runTraceProbImpl]
  | inr mc =>
      by_cases hcache : s mc = none
      · simp [runTraceProbImpl, hcache, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
          monadLift_self, uniformSampleImpl]
      · rcases Option.ne_none_iff_exists.mp hcache with ⟨ω, hω⟩
        simp [runTraceProbImpl, hω.symm, StateT.run_bind, StateT.run_get]

/-!
#### Phase D: fork bridge

Phase D is now the clean live-verification bridge. `managedRoNmaExp nmaAdv` and
`Fork.exp σ hr M nmaAdv qH` run the same adversary against the same live random-oracle
semantics; `Fork.exp` only adds the `forkPoint` check needed for rewinding.

Under the hash-query bound, `runTrace`'s explicit terminal verification query ensures the
forged point is logged, so successful live verification implies that `forkPoint` is
present as well. Accordingly the core Phase D lemma is the exact inequality
`managedRoNmaAdv.advantage ≤ Fork.advantage`.

Any `collisionSlack qS qH β` bookkeeping belongs to the earlier simulation phase,
not to the fork bridge itself. -/
set_option maxHeartbeats 2000000 in -- Phase D: large `simulateQ` / `StateT` / `bind` proof
set_option linter.flexible false in
omit [Fintype Chal] in
/-- The managed-RO NMA experiment and `Fork.exp` agree on verification semantics:
both use the same adversary, both implement a consistent random oracle, and both
perform live verification. `Fork.exp` additionally checks `forkPoint`, which
requires verification AND the hash point appearing in the query log within the
first `qH + 1` entries. Under the hash-query bound (at most `qH` adversary hash
queries), `runTrace`'s explicit final query ensures the hash point is always
logged, so `forkPoint` succeeds whenever verification does.

This gives `managedRoNmaAdv.advantage ≤ Fork.advantage`, making Phase D trivially
true with `collisionSlack` as free slack. -/
lemma nma_advantage_le_fork_advantage (qH : ℕ)
    (hBound : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (nmaAdvFromHVZK σ hr M simTranscript adv).main pk) qH) :
    SignatureAlg.managedRoNmaAdv.advantage (runtime M)
        (nmaAdvFromHVZK σ hr M simTranscript adv) ≤
      Fork.advantage σ hr M (nmaAdvFromHVZK σ hr M simTranscript adv) qH := by
  set nmaAdv := nmaAdvFromHVZK σ hr M simTranscript adv
  let verifiedExp : ProbComp Bool :=
    let chalSpec : OracleSpec Unit := Unit →ₒ Chal
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl) do
      let (pk, _) ← OracleComp.liftComp hr.gen (unifSpec + chalSpec)
      let trace ← Fork.runTrace σ hr M nmaAdv pk
      pure trace.verified
  have hManagedEq : SignatureAlg.managedRoNmaAdv.advantage (runtime M) nmaAdv =
      Pr[= true | verifiedExp] := by
    let instM : DecidableEq M := inferInstance
    let instCommit : DecidableEq Commit := inferInstance
    classical
    letI : DecidableEq M := Classical.decEq M
    letI : DecidableEq Commit := Classical.decEq Commit
    unfold SignatureAlg.managedRoNmaAdv.advantage
    let runtimeImpl :
        QueryImpl (unifSpec + (M × Commit →ₒ Chal))
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
      (QueryImpl.id' unifSpec).liftTarget
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) +
        (randomOracle (spec := (M × Commit →ₒ Chal)))
    have hManagedBind :
        SignatureAlg.managedRoNmaExp (runtime M) nmaAdv =
          (ProbCompRuntime.probComp.evalDist <| hr.gen >>= fun pkw =>
            StateT.run'
              (simulateQ runtimeImpl (do
                let result ← nmaAdv.main pkw.1
                let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                  (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                  (result.1.1, result.1.2.1)
                pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
              ∅) := by
      let rhsComp : ProbComp Bool :=
        hr.gen >>= fun pkw =>
          StateT.run' (simulateQ runtimeImpl (do
            let result ← nmaAdv.main pkw.1
            let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
              (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
              (result.1.1, result.1.2.1)
            pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2))) ∅
      have hEq :
          StateT.run' (simulateQ runtimeImpl (do
            let __discr ← monadLift hr.gen
            let result ← nmaAdv.main __discr.1
            let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
              (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
              (result.1.1, result.1.2.1)
            pure (σ.verify __discr.1 result.1.2.1 r' result.1.2.2))) ∅ = rhsComp := by
        simp only [runtimeImpl, rhsComp, simulateQ_bind]
        simpa [runtimeImpl, unifFwdImpl] using
          (roSim.run'_liftM_bind (hashSpec := (M × Commit →ₒ Chal))
            (ro := (randomOracle (spec := (M × Commit →ₒ Chal))))
            (oa := hr.gen)
            (rest := fun pkw =>
              simulateQ runtimeImpl (do
                let result ← nmaAdv.main pkw.1
                let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                  (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                  (result.1.1, result.1.2.1)
                pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
            (s := ∅))
      unfold SignatureAlg.managedRoNmaExp FiatShamir.runtime ProbCompRuntime.evalDist
        SPMFSemantics.evalDist SemanticsVia.denote
      simp only [SPMFSemantics.withStateOracle, StateT.run'_eq, FiatShamir, runtimeImpl]
      simpa [rhsComp, runtimeImpl, QueryImpl.ofLift_eq_id', ProbCompRuntime.probComp,
          ProbCompRuntime.evalDist, SPMFSemantics.evalDist, SPMFSemantics.ofHasEvalSPMF,
          SemanticsVia.denote, StateT.run'_eq] using
        congrArg (HasEvalSPMF.toSPMF.toFun Bool) hEq
    have hManagedBindProb := congrArg (fun x => probOutput x true) hManagedBind
    calc
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M) nmaAdv] =
          Pr[= true | ProbCompRuntime.probComp.evalDist <| hr.gen >>= fun pkw =>
            StateT.run'
              (simulateQ runtimeImpl (do
                let result ← nmaAdv.main pkw.1
                let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                  (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                  (result.1.1, result.1.2.1)
                pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
              ∅] := by
            simpa using hManagedBindProb
      _ = Pr[= true | verifiedExp] := by
        unfold verifiedExp
        simp only [QueryImpl.simulateQ_add_liftComp_left, simulateQ_ofLift_eq_self, simulateQ_bind,
          simulateQ_pure]
        have hStep :
            Pr[= true | hr.gen >>= fun pkw =>
              StateT.run'
                (simulateQ runtimeImpl (do
                  let result ← nmaAdv.main pkw.1
                  let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                    (result.1.1, result.1.2.1)
                  pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
                ∅] =
            Pr[= true | do
              let x ← hr.gen
              let x ← simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl)
                (@Fork.runTrace Stmt Wit Commit PrvState Chal Resp rel σ hr M
                  instM instCommit (inferInstance : SampleableType Chal) nmaAdv x.1)
              pure x.verified] := by
          apply probOutput_bind_congr
          intro pkw hpkw
          let wrappedMain :
              OracleComp (unifSpec + (M × Commit →ₒ Chal))
                (((M × Commit × Resp) × (unifSpec + (M × Commit →ₒ Chal)).QueryCache) × Chal) := do
            let result@(forgery, _) ← nmaAdv.main pkw.1
            match forgery with
            | (msg, (c, _)) =>
                let ω : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                  (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) (msg, c)
                pure (result, ω)
          let verifyFn :
              (((M × Commit × Resp) ×
                  (unifSpec + (M × Commit →ₒ Chal)).QueryCache) × Chal) → Bool :=
            fun z => σ.verify pkw.1 z.1.1.2.1 z.2 z.1.1.2.2
          have hprojRun :
              Prod.map id Prod.fst <$>
                  (simulateQ
                      (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) wrappedMain).run
                    (∅, []) =
                (simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                  wrappedMain).run ∅ := by
            simpa [wrappedMain] using
              (OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                (impl₂ := runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                (proj := Prod.fst)
                (hproj := runTraceImpl_proj_eq (M := M) (Commit := Commit) (Chal := Chal))
                wrappedMain (∅, []))
          have hcomp :
              simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                ((simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                  wrappedMain).run' ∅) =
                (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
                  wrappedMain).run' ∅ := by
            have hrun :=
              runTraceProbImpl_run_eq (M := M) (Commit := Commit) (Chal := Chal)
                (oa := wrappedMain) (cache := ∅)
            have hmap := congrArg (fun p => Prod.fst <$> p) hrun
            simpa [StateT.run', simulateQ_map] using hmap.symm
          have hLeftPk :
              StateT.run' (simulateQ runtimeImpl (do
                let result ← nmaAdv.main pkw.1
                let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                  (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                  (result.1.1, result.1.2.1)
                pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2))) ∅ =
                verifyFn <$>
                  (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
                      wrappedMain).run' ∅ := by
            calc
              StateT.run' (simulateQ runtimeImpl (do
                let result ← nmaAdv.main pkw.1
                let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                  (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                  (result.1.1, result.1.2.1)
                pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2))) ∅
                  = StateT.run' (simulateQ runtimeImpl (verifyFn <$> wrappedMain)) ∅ := by
                      simp [wrappedMain, verifyFn]
              _ =
                verifyFn <$>
                  (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
                      wrappedMain).run' ∅ := by
                      rw [simulateQ_map]
                      simpa [runtimeImpl, wrappedMain, verifyFn] using
                        (congrArg (fun mx => verifyFn <$> mx)
                          (runTraceProbImpl_run'_eq_runtime (M := M) (Commit := Commit)
                              (Chal := Chal) (oa := wrappedMain) (cache := ∅))).symm
          letI : DecidableEq M := instM
          letI : DecidableEq Commit := instCommit
          have hprojRun' :
              Prod.map id Prod.fst <$>
                  (simulateQ
                      (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal) wrappedMain).run
                    (∅, []) =
                (simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                  wrappedMain).run ∅ := by
            simpa [wrappedMain] using
              (OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                (impl₂ := runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                (proj := Prod.fst)
                (hproj := runTraceImpl_proj_eq (M := M) (Commit := Commit) (Chal := Chal))
                wrappedMain (∅, []))
          have hcomp' :
              simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                ((simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                  wrappedMain).run' ∅) =
                (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
                  wrappedMain).run' ∅ := by
            have hrun :=
              runTraceProbImpl_run_eq (M := M) (Commit := Commit) (Chal := Chal)
                (oa := wrappedMain) (cache := ∅)
            have hmap := congrArg (fun p => Prod.fst <$> p) hrun
            simpa [StateT.run', simulateQ_map] using hmap.symm
          have hRightPk :
              (do
                let trace ← simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl)
                  (@Fork.runTrace Stmt Wit Commit PrvState Chal Resp rel σ hr M
                    instM instCommit (inferInstance : SampleableType Chal) nmaAdv pkw.1)
                pure trace.verified) =
                verifyFn <$>
                  (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
                      wrappedMain).run' ∅ := by
            have hprojRunMap :
                verifyFn <$> simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                  (Prod.fst <$>
                    (simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                        wrappedMain).run
                      (∅, [])) =
                  verifyFn <$> simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                    ((simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                          wrappedMain).run' ∅) := by
              simpa [StateT.run'] using
                congrArg (fun mx =>
                  verifyFn <$> simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                    (Prod.fst <$> mx)) hprojRun'
            calc
              (do
                let trace ← simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl)
                  (@Fork.runTrace Stmt Wit Commit PrvState Chal Resp rel σ hr M
                    instM instCommit (inferInstance : SampleableType Chal) nmaAdv pkw.1)
                pure trace.verified)
                  =
                verifyFn <$> simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                  (Prod.fst <$>
                    (simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                        wrappedMain).run
                      (∅, [])) := by
                    simp [Fork.runTrace, wrappedMain, verifyFn, simulateQ_map,
                      QueryImpl.ofLift_eq_id']
                    refine bind_congr (m := ProbComp) fun a => ?_
                    have hro :
                        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                          ((Fork.roImpl M Commit Chal (a.1.1.1, a.1.1.2.1)).run a.2) =
                        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                          ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                            (liftM (query (a.1.1.1, a.1.1.2.1)))).run a.2) := by
                      have hinner :
                          (Fork.roImpl M Commit Chal (a.1.1.1, a.1.1.2.1)).run a.2 =
                          (simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                            (liftM (query (a.1.1.1, a.1.1.2.1)))).run a.2 := by
                        have hquery :
                            simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                              (liftM (query (spec := (M × Commit →ₒ Chal))
                                (a.1.1.1, a.1.1.2.1))) =
                              Fork.roImpl M Commit Chal (a.1.1.1, a.1.1.2.1) := by
                          simpa [-simulateQ_query, QueryImpl.add_apply_inr] using
                            (simulateQ_query
                              (impl := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
                              (q := (query (spec := (M × Commit →ₒ Chal))
                                (a.1.1.1, a.1.1.2.1))))
                        exact congrArg (fun st => st.run a.2) hquery.symm
                      simp [hinner]
                    simpa [map_eq_bind_pure_comp] using
                      congrArg (fun mx =>
                        mx >>= pure ∘ fun a_1 =>
                          σ.verify pkw.1 a.1.1.2.1 a_1.1 a.1.1.2.2) hro
              _ =
                verifyFn <$> simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
                  ((simulateQ (runTraceImplNoLog (M := M) (Commit := Commit) (Chal := Chal))
                    wrappedMain).run' ∅) := hprojRunMap
              _ =
                verifyFn <$>
                  (simulateQ (runTraceProbImpl (M := M) (Commit := Commit) (Chal := Chal))
                      wrappedMain).run' ∅ := by
                    rw [hcomp']
          rw [hLeftPk, hRightPk]
          have hRunTraceProbEq :
              (simulateQ
                  (@runTraceProbImpl Commit Chal M (Classical.decEq M) (Classical.decEq Commit)
                    (inferInstance : SampleableType Chal)) wrappedMain).run' ∅ =
              (simulateQ (@runTraceProbImpl Commit Chal M instM instCommit
                    (inferInstance : SampleableType Chal)) wrappedMain).run' ∅ := by
            refine OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq'
              (impl₁ := @runTraceProbImpl Commit Chal M (Classical.decEq M)
                (Classical.decEq Commit) (inferInstance : SampleableType Chal))
              (impl₂ := @runTraceProbImpl Commit Chal M instM instCommit
                (inferInstance : SampleableType Chal))
              (proj := id) ?_ wrappedMain ∅
            intro t s
            cases t with
            | inl n =>
                simp [runTraceProbImpl]
            | inr mc =>
                by_cases hcache : s mc = none
                · simp [runTraceProbImpl, hcache, StateT.run_bind, StateT.run_get,
                    StateT.run_monadLift, monadLift_self]
                  refine congrArg (fun f => f <$> ($ᵗ Chal)) ?_
                  funext a
                  refine Prod.ext rfl ?_
                  funext mc'
                  by_cases hEq : mc' = mc
                  · subst hEq
                    simp [QueryCache.cacheQuery]
                  · simp [QueryCache.cacheQuery, hEq]
                · rcases Option.ne_none_iff_exists.mp hcache with ⟨ω, hω⟩
                  simp [runTraceProbImpl, hω.symm, StateT.run_bind, StateT.run_get]
          simpa using congrArg (fun mx => Pr[= true | verifyFn <$> mx]) hRunTraceProbEq
        have hManagedNormalize :
            Pr[= true |
                ProbCompRuntime.probComp.evalDist do
                  let pkw ← hr.gen
                  (do
                      let x ← simulateQ runtimeImpl (nmaAdv.main pkw.1)
                      let x_1 : Chal ← simulateQ runtimeImpl
                        (HasQuery.query (spec := (M × Commit →ₒ Chal))
                          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                          (x.1.1, x.1.2.1))
                      pure (σ.verify pkw.1 x.1.2.1 x_1 x.1.2.2)).run' ∅] =
            Pr[= true | hr.gen >>= fun pkw =>
              StateT.run'
                (simulateQ runtimeImpl (do
                  let result ← nmaAdv.main pkw.1
                  let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                    (result.1.1, result.1.2.1)
                  pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
                ∅] := by
          change Pr[= true | do
              let pkw ← hr.gen
              (do
                  let x ← simulateQ runtimeImpl (nmaAdv.main pkw.1)
                  let x_1 : Chal ← simulateQ runtimeImpl
                    (HasQuery.query (spec := (M × Commit →ₒ Chal))
                      (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                      (x.1.1, x.1.2.1))
                  pure (σ.verify pkw.1 x.1.2.1 x_1 x.1.2.2)).run' ∅] =
            Pr[= true | hr.gen >>= fun pkw =>
              StateT.run'
                (simulateQ runtimeImpl (do
                  let result ← nmaAdv.main pkw.1
                  let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                    (result.1.1, result.1.2.1)
                  pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
                ∅]
          have hManagedComp :
              (do
                let pkw ← hr.gen
                (do
                    let x ← simulateQ runtimeImpl (nmaAdv.main pkw.1)
                    let x_1 : Chal ← simulateQ runtimeImpl
                      (HasQuery.query (spec := (M × Commit →ₒ Chal))
                        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                        (x.1.1, x.1.2.1))
                    pure (σ.verify pkw.1 x.1.2.1 x_1 x.1.2.2)).run' ∅) =
              (hr.gen >>= fun pkw =>
                StateT.run'
                  (simulateQ runtimeImpl (do
                    let result ← nmaAdv.main pkw.1
                    let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                      (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                      (result.1.1, result.1.2.1)
                    pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
                  ∅) := by
            simp [simulateQ_bind]
          exact congrArg (fun mx => Pr[= true | mx]) hManagedComp
        have hStep' :
            Pr[= true | hr.gen >>= fun pkw =>
              StateT.run'
                (simulateQ runtimeImpl (do
                  let result ← nmaAdv.main pkw.1
                  let r' : Chal ← HasQuery.query (spec := (M × Commit →ₒ Chal))
                    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
                    (result.1.1, result.1.2.1)
                  pure (σ.verify pkw.1 result.1.2.1 r' result.1.2.2)))
                ∅] =
            Pr[= true | do
              let x ← hr.gen
              let x ← simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl)
                (@Fork.runTrace Stmt Wit Commit PrvState Chal Resp rel σ hr M
                  instM instCommit (inferInstance : SampleableType Chal) nmaAdv x.1)
              pure x.verified] := by
          simpa using hStep
        exact hManagedNormalize.trans hStep'
  have hVerifiedLe : Pr[= true | verifiedExp] ≤ Fork.advantage σ hr M nmaAdv qH := by
    classical
    unfold verifiedExp Fork.advantage Fork.exp
    simp only [simulateQ_bind, QueryImpl.simulateQ_add_liftComp_left, simulateQ_ofLift_eq_self]
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    apply probEvent_bind_mono
    intro pkw hpkw
    set runPk :
        ProbComp (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
      simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl)
        (Fork.runTrace σ hr M nmaAdv pkw.1)
    change Pr[ fun x => x = true | (fun trace => trace.verified) <$> runPk] ≤
      Pr[ fun x => x = true |
        (fun trace => (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
          (Chal := Chal) qH trace).isSome) <$> runPk]
    rw [probEvent_map, probEvent_map]
    refine probEvent_mono ?_
    intro trace htrace hverified
    have htrace' :
        trace ∈ support (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (Fork.runTrace σ hr M nmaAdv pkw.1)) := by
      simpa [runPk, QueryImpl.ofLift_eq_id'] using htrace
    have htraceRun : trace ∈ support (Fork.runTrace σ hr M nmaAdv pkw.1) := by
      rw [support_simulateQ_unifChalImpl (oa := Fork.runTrace σ hr M nmaAdv pkw.1)] at htrace'
      exact htrace'
    have htraceReplay :
        trace ∈ support (Prod.fst <$> replayFirstRun (Fork.runTrace σ hr M nmaAdv pkw.1)) := by
      simpa using htraceRun
    rw [support_map] at htraceReplay
    obtain ⟨z, hz, hzEq⟩ := htraceReplay
    rcases z with ⟨trace', outerLog⟩
    have hEq : trace' = trace := by
      simpa using hzEq
    subst hEq
    exact runTrace_verified_imp_forkPoint (σ := σ) (hr := hr) (M := M) (Chal := Chal)
      nmaAdv qH hBound pkw.1 hz hverified
  simpa [nmaAdv] using hManagedEq.trans_le hVerifiedLe

omit [Fintype Chal] in
lemma game2_le_fork_advantage_plus_collision (β : ℝ≥0∞)
    (_hβ : SigmaProtocol.simCommitPredictability simTranscript β) (qS qH : ℕ)
    (hNmaBound : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (nmaAdvFromHVZK σ hr M simTranscript adv).main pk) qH) :
    SignatureAlg.managedRoNmaAdv.advantage (runtime M)
        (nmaAdvFromHVZK σ hr M simTranscript adv) ≤
      Fork.advantage σ hr M (nmaAdvFromHVZK σ hr M simTranscript adv) qH +
        collisionSlack qS qH β := by
  calc SignatureAlg.managedRoNmaAdv.advantage (runtime M)
          (nmaAdvFromHVZK σ hr M simTranscript adv)
      ≤ Fork.advantage σ hr M (nmaAdvFromHVZK σ hr M simTranscript adv) qH :=
          nma_advantage_le_fork_advantage σ hr M simTranscript adv qH hNmaBound
    _ ≤ Fork.advantage σ hr M (nmaAdvFromHVZK σ hr M simTranscript adv) qH +
          collisionSlack qS qH β :=
          le_add_right le_rfl

end NmaPhases

/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B) + qS · ζ_zk + qS · (qS + qH) · β`

where `β` is the predictability of the simulator's commitment marginal (see
`SigmaProtocol.simCommitPredictability`).

The NMA adversary `B` is constructed by:
- Forwarding `A`'s hash queries to the external oracle (visible to `Fork.fork`)
- Simulating `A`'s signing queries using the HVZK simulator, programming the
  simulated challenge into the cache
- Returning `A`'s forgery together with the accumulated `QueryCache`

Each of the `qS` signing simulations introduces at most `ζ_zk` total-variation distance;
the birthday term `collisionSlack qS qH β` absorbs collisions where `A` queries a
hash that `B` later programs.

The bound decomposes into two live-facing phases, each extracted as its own
lemma and chained in the final `calc`:

- `hybrid_sign_le` (**Phase C**, remaining proof obligation):
  `Adv^{EUF-CMA}(A) ≤ Adv^{managed-RO-NMA}(B) + qS · ζ_zk + collisionSlack qS qH β`.
  Internally this keeps the freshness bit through the HVZK replacement and pays
  `collisionSlack` only when bridging the simulator's `bad ∨ freshSuccess` event
  back to the canonical live managed-RO experiment.
- `nma_advantage_le_fork_advantage` (**Phase D**, live fork bridge):
  `Adv^{managed-RO-NMA}(B) ≤ Adv^{fork-NMA}_{qH}(B)`.
  Once Phase C has already paid for the programmed-cache mismatch, the remaining
  bridge to `Fork.advantage` is fully live.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`.

The Lean bound generalizes Firsov-Janku's `pr_koa_cma` at
[fsec/proof/Schnorr.ec:943](../../../fsec/proof/Schnorr.ec): EasyCrypt inlines the Schnorr
simulator to obtain `β = 1/|Ω|`; we instead take `β` as a hypothesis
(`SigmaProtocol.simCommitPredictability`), making the theorem generic over all Sigma protocols
with bounded commitment predictability. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (β : ℝ≥0∞) (_hβ : SigmaProtocol.simCommitPredictability simTranscript β)
    (ζ_zk : ℝ) (_hζ_zk : 0 ≤ ζ_zk)
    (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal (qS * ζ_zk) +
          collisionSlack qS qH β := by
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none =>
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  have hNmaBound : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (nmaAdvFromHVZK σ hr M simTranscript adv).main pk) qH := by
    -- Query bound: show the NMA adversary makes at most `qH` hash queries.
    -- `fwd` forwards each hash query as-is (1 hash query per CMA hash query).
    -- `sigSim` handles signing queries via `simTranscript` + cache programming,
    -- generating zero hash queries (only uniform queries from `simTranscript`).
    -- Requires a general `IsQueryBound` transfer lemma for `simulateQ` + `StateT.run`.
    intro pk
    let stepBudget :
        (spec + (M →ₒ (Commit × Resp))).Domain → ℕ × ℕ → ℕ := fun t _ =>
      match t with
      | .inl (.inl _) => 0
      | .inl (.inr _) => 1
      | .inr _ => 0
    have hbind :
        ∀ {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {Q₁ Q₂ : ℕ},
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁ →
          (∀ x, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ob x) Q₂) →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := oa >>= ob) (Q₁ + Q₂) := by
      intro α β oa ob Q₁ Q₂ h1 h2
      exact nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal) h1 h2
    have hfwd :
        ∀ (t : spec.Domain) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (fwd t).run s) (match t with
              | .inl _ => 0
              | .inr _ => 1) := by
      intro t s
      cases t with
      | inl n =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (query (spec := spec) (.inl n))) 0 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inl n) 0).2 trivial)
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
      | inr mc =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (query (spec := spec) (.inr mc))) 1 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inr mc) 1).2 (Nat.succ_pos 0))
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
    have hro :
        ∀ (mc : M × Commit) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (roSim mc).run s) 1 := by
      intro mc s
      cases hs : s (.inr mc) with
      | some v =>
          simp [roSim, hs, nmaHashQueryBound]
      | none =>
          simpa [roSim, hs] using
            ((OracleComp.isQueryBound_map_iff
                (oa := (fwd (.inr mc)).run s)
                (f := fun a : Chal × spec.QueryCache =>
                  (a.1, a.2.cacheQuery (.inr mc) a.1))
                (b := 1)
                (canQuery := fun t b => match t with
                  | .inl _ => True
                  | .inr _ => 0 < b)
                (cost := fun t b => match t with
                  | .inl _ => b
                  | .inr _ => b - 1)).2
              (hfwd (.inr mc) s))
    have hsig :
        ∀ (msg : M) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (sigSim pk msg).run s) 0 := by
      intro msg s
      have hsource : OracleComp.IsQueryBound
          (simTranscript pk) () (fun _ _ => True) (fun _ _ => ()) := by
        induction simTranscript pk using OracleComp.inductionOn with
        | pure x =>
            trivial
        | query_bind t mx ih =>
            simp [OracleComp.isQueryBound_query_bind_iff, ih]
      have htranscript :
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (simulateQ unifSim (simTranscript pk)).run s) 0 := by
        simpa [nmaHashQueryBound] using
          (OracleComp.IsQueryBound.simulateQ_run_of_step
            (h := hsource) (combine := Nat.add) (mapBudget := fun _ => 0)
            (stepBudget := fun _ _ => 0) (impl := unifSim)
            (hbind := by
              intro γ δ oa' ob b₁ b₂ h1 h2
              have h1' :
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := oa') b₁ := by
                simpa [nmaHashQueryBound] using h1
              have h2' : ∀ x,
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := ob x) b₂ := by
                intro x
                simpa [nmaHashQueryBound] using h2 x
              simpa [nmaHashQueryBound] using
                (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
            )
            (hstep := by
              intro t b s' ht
              simpa [unifSim] using hfwd (.inl t) s')
            (hcombine := by
              intro t b ht
              simp)
            (s := s))
      simpa [sigSim, nmaHashQueryBound] using
        ((OracleComp.isQueryBound_map_iff
            (oa := (simulateQ unifSim (simTranscript pk)).run s)
            (f := fun a : (Commit × Chal × Resp) × spec.QueryCache =>
              ((a.1.1, a.1.2.2),
                QueryCache.cacheQuery a.2 (.inr (msg, a.1.1)) a.1.2.1))
            (b := 0)
            (canQuery := fun t b => match t with
              | .inl _ => True
              | .inr _ => 0 < b)
            (cost := fun t b => match t with
              | .inl _ => b
              | .inr _ => b - 1)).2 htranscript)
    have hstep :
        ∀ t b s,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ((baseSim + sigSim pk) t).run s) (stepBudget t b) := by
      intro t b s ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simpa [baseSim, stepBudget] using hfwd (.inl n) s
          | inr mc =>
              simpa [baseSim, stepBudget] using hro mc s
      | inr msg =>
          simpa [stepBudget] using hsig msg s
    have hcombine :
        ∀ t b,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          Nat.add (stepBudget t b)
            (Prod.snd (match t, b with
              | .inl (.inl _), b' => b'
              | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
              | .inr _, (qS', qH') => (qS' - 1, qH'))) =
            Prod.snd b := by
      intro t b ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simp [stepBudget]
          | inr mc =>
              simp [stepBudget] at ht ⊢
              omega
      | inr msg =>
          simp [stepBudget]
    simpa [nmaHashQueryBound, signHashQueryBound] using
      (OracleComp.IsQueryBound.simulateQ_run_of_step
        (h := _hQ pk) (combine := Nat.add) (mapBudget := Prod.snd)
        (stepBudget := stepBudget) (impl := baseSim + sigSim pk)
        (hbind := by
          intro γ δ oa' ob b₁ b₂ h1 h2
          have h1' :
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := oa') b₁ := by
            simpa [nmaHashQueryBound] using h1
          have h2' : ∀ x,
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := ob x) b₂ := by
            intro x
            simpa [nmaHashQueryBound] using h2 x
          simpa [nmaHashQueryBound] using
            (hbind (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
        )
        (hstep := by
          intro t b s ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hfwd (.inl n) s
              | inr mc =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hro mc s
          | inr msg =>
              simpa [nmaHashQueryBound, stepBudget] using hsig msg s)
        (hcombine := by
          intro t b ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simp [stepBudget]
              | inr mc =>
                  simp [stepBudget] at ht ⊢
                  omega
          | inr msg =>
              simp [stepBudget])
        (s := ∅))
  refine ⟨nmaAdvFromHVZK σ hr M simTranscript adv, hNmaBound, ?_⟩
  -- Advantage bound: chain the three phase lemmas.
  --   `adv.advantage`
  --       ≤ `Pr[= true | Game 1]`                     (Phase B: freshness drop)
  --       ≤ `managedRoNmaAdvantage + qS · ζ_zk + collisionSlack`
  --                                   (Phase C: freshness-aware hybrid + bridge)
  --       ≤ `Fork.advantage + qS · ζ_zk + collisionSlack`
  --                                                 (Phase D: live fork bridge)
  calc adv.advantage (runtime M)
      ≤ SignatureAlg.managedRoNmaAdv.advantage (runtime M)
            (nmaAdvFromHVZK σ hr M simTranscript adv) +
          ENNReal.ofReal (qS * ζ_zk) +
          collisionSlack qS qH β :=
        hybrid_sign_le σ hr M simTranscript ζ_zk adv β _hβ _hζ_zk _hhvzk qS qH _hQ
    _ ≤ Fork.advantage σ hr M (nmaAdvFromHVZK σ hr M simTranscript adv) qH +
          ENNReal.ofReal (qS * ζ_zk) +
          collisionSlack qS qH β := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (add_le_add_right
              (nma_advantage_le_fork_advantage σ hr M simTranscript adv qH hNmaBound)
              (ENNReal.ofReal (qS * ζ_zk)))
            (collisionSlack qS qH β)

section evalDistBridge

variable [Fintype Chal] [Inhabited Chal] [SampleableType Chal]

/-- The `ofLift + uniformSampleImpl` simulation on `unifSpec + (Unit →ₒ Chal)` preserves
`evalDist`. Both oracle components sample uniformly from their range (the `unifSpec`
side via `liftM (query n) : ProbComp (Fin (n+1))`, the challenge side via `$ᵗ Chal`),
so the simulated computation has the same distribution as the source. -/
private lemma evalDist_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) :
    evalDist (simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rcases t with n | u
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        id_map, evalDist_bind, ih]
      apply bind_congr
      simp
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inr, uniformSampleImpl,
        id_map, evalDist_bind, ih]
      have heq : (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
            SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
          (evalDist (liftM (query (Sum.inr u)) :
            OracleComp (unifSpec + (Unit →ₒ Chal)) _) :
            SPMF ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr u))) := by
        rw [evalDist_uniformSample, evalDist_query]; rfl
      exact heq ▸ rfl

/-- Corollary: `probEvent` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probEvent_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (p : α → Prop) :
    Pr[ p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator]
  refine tsum_congr fun x => ?_
  unfold Set.indicator
  split_ifs with hpx
  · exact congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x
  · rfl

/-- Corollary: `probOutput` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probOutput_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (x : α) :
    Pr[= x | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x

end evalDistBridge
section jensenIntegration

/-- **Keygen-indexed Cauchy-Schwarz / Jensen step for the forking lemma.**

Given a per-element bound `acc x · (acc x / q - hinv) ≤ B x`, integrating over a
probabilistic key-generator `gen : ProbComp X` yields the "lifted" bound:

  `μ · (μ / q - hinv) ≤ 𝔼[B]`

where `μ = 𝔼[acc] = ∑' x, Pr[= x | gen] · acc x`.

The proof goes through the convexity identity `μ² ≤ 𝔼[acc²]` (Cauchy-Schwarz on the
probability distribution `Pr[= · | gen]`), together with `ENNReal.mul_sub` to handle the
truncated subtraction. -/
private lemma jensen_keygen_forking_bound
    {X : Type} (gen : ProbComp X)
    (acc B : X → ENNReal) (q hinv : ENNReal)
    (hinv_ne_top : hinv ≠ ⊤)
    (hacc_le : ∀ x, acc x ≤ 1)
    (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∑' x, Pr[= x | gen] * acc x) *
        ((∑' x, Pr[= x | gen] * acc x) / q - hinv) ≤
      ∑' x, Pr[= x | gen] * B x := by
  classical
  set w : X → ENNReal := fun x => Pr[= x | gen] with hw_def
  set μ : ENNReal := ∑' x, w x * acc x with hμ_def
  have hw_tsum_le_one : ∑' x, w x ≤ 1 := tsum_probOutput_le_one
  have hμ_le_one : μ ≤ 1 := by
    calc μ = ∑' x, w x * acc x := rfl
      _ ≤ ∑' x, w x * 1 := by gcongr with x; exact hacc_le x
      _ = ∑' x, w x := by simp
      _ ≤ 1 := hw_tsum_le_one
  have hμ_ne_top : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le_one
  -- The integrand `w x * acc x * hinv`, with total sum `μ * hinv`.
  have hμ_hinv_ne_top : μ * hinv ≠ ⊤ := ENNReal.mul_ne_top hμ_ne_top hinv_ne_top
  -- Cauchy-Schwarz: `μ² ≤ ∑' w * acc²`.
  have hCS : μ ^ 2 ≤ ∑' x, w x * acc x ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w acc hw_tsum_le_one
  -- Split off the key reverse-Jensen inequality as an intermediate calc.
  -- Integrate the per-element bound.
  calc μ * (μ / q - hinv)
      = μ * (μ / q) - μ * hinv :=
        ENNReal.mul_sub (fun _ _ => hμ_ne_top)
    _ = μ ^ 2 / q - μ * hinv := by
        rw [sq, mul_div_assoc]
    _ ≤ (∑' x, w x * acc x ^ 2) / q - μ * hinv := by
        gcongr
    _ = (∑' x, w x * acc x ^ 2 / q) - ∑' x, w x * acc x * hinv := by
        congr 1
        · simp only [div_eq_mul_inv]
          rw [ENNReal.tsum_mul_right]
        · rw [hμ_def, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, (w x * acc x ^ 2 / q - w x * acc x * hinv) := by
        -- Reverse-Jensen: `∑' f - ∑' g ≤ ∑' (f - g)` in ENNReal when `∑' g ≠ ⊤`.
        set f : X → ENNReal := fun x => w x * acc x ^ 2 / q with hf_def
        set g : X → ENNReal := fun x => w x * acc x * hinv with hg_def
        have hg_sum_ne_top : ∑' x, g x ≠ ⊤ := by
          change ∑' x, w x * acc x * hinv ≠ ⊤
          rw [ENNReal.tsum_mul_right]; exact hμ_hinv_ne_top
        have hfg : ∑' x, f x ≤ ∑' x, (f x - g x) + ∑' x, g x := by
          calc ∑' x, f x ≤ ∑' x, ((f x - g x) + g x) := by
                exact ENNReal.tsum_le_tsum fun x => le_tsub_add
            _ = ∑' x, (f x - g x) + ∑' x, g x := ENNReal.tsum_add
        exact tsub_le_iff_right.2 hfg
    _ = ∑' x, w x * (acc x ^ 2 / q - acc x * hinv) := by
        refine tsum_congr fun x => ?_
        have hwx_ne_top : w x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
        rw [ENNReal.mul_sub (fun _ _ => hwx_ne_top), mul_div_assoc, mul_assoc]
    _ = ∑' x, w x * (acc x * (acc x / q - hinv)) := by
        refine tsum_congr fun x => ?_
        have hax_ne_top : acc x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (hacc_le x)
        congr 1
        rw [ENNReal.mul_sub (fun _ _ => hax_ne_top), sq, mul_div_assoc]
    _ ≤ ∑' x, w x * B x := by
        gcongr with x
        exact hper x

end jensenIntegration

section eufNmaHelpers

variable [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]

/-- Replay-fork query budget for the NMA reduction: forward the `.inl unifSpec` component
live (budget `0`) and rewind only the counted challenge oracle on the `.inr` side, capped
at `qH` queries. -/
private def nmaForkBudget (qH : ℕ) : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => qH

/-- Per-run invariant for the NMA replay fork. If `Fork.forkPoint qH` selects index `s`,
the cached RO value at `x.target`, the outer log's `s`-th counted-oracle response, and the
challenge under which `x.forgery` verifies all coincide.

Holding this for both fork runs lets `Fork.replayForkingBound` deliver two accepting
transcripts with the same commitment and distinct challenges, precisely what special
soundness needs. -/
private def forkSupportInvariant
    (qH : ℕ) (pk : Stmt)
    (x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (log : QueryLog (unifSpec + (Unit →ₒ Chal))) : Prop :=
  ∀ s : Fin (qH + 1),
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x =
        some s →
    ∃ ω : Chal,
      QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
      x.roCache x.target = some ω ∧
      σ.verify pk x.target.2 ω x.forgery.2.2 = true

variable [SampleableType Chal] [Fintype Chal] [Inhabited Chal]

/-- Witness-extraction computation over `unifSpec + (Unit →ₒ Chal)` used by the NMA
reduction. Replay-forks the wrapped adversary at the counted challenge oracle, matches
the two forgeries against the sigma-protocol extractor when the commitments agree and
the cached challenges differ, and falls back to a uniform witness otherwise. -/
private noncomputable def eufNmaForkExtract
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt) :
    OracleComp (unifSpec + (Unit →ₒ Chal)) Wit := do
  let result ← forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)
  match result with
  | none => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
  | some (x₁, x₂) =>
    let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
    let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
    if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
          if _hω : ω₁ ≠ ω₂ then
            liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + (Unit →ₒ Chal))
          else
            liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
      | _, _ => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
    else
      liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))

/-- NMA reduction for `euf_nma_bound`: simulate the challenge oracle of
`eufNmaForkExtract` down to `ProbComp`. -/
private noncomputable def eufNmaReduction
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : Stmt → ProbComp Wit := fun pk =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))) (eufNmaForkExtract σ hr M nmaAdv qH pk)

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] [Fintype Chal] in
/-- **Support invariant of the replay-fork first run.**

Every `(x, log)` in the support of `replayFirstRun (Fork.runTrace σ hr M nmaAdv pk)`
satisfies the per-run invariant `forkSupportInvariant`: at a valid fork point, the cached
RO challenge matches the outer log entry and the forgery verifies. -/
private theorem forkSupportInvariant_of_mem_replayFirstRun
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {log : QueryLog (unifSpec + (Unit →ₒ Chal))}
    (h : (x, log) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    forkSupportInvariant σ M qH pk x log := by
  classical
  intro s hs
  have htarget : x.queryLog[(↑s : ℕ)]? = some x.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hverified : x.verified = true :=
    Fork.forkPoint_some_imp_verified (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hslt : (↑s : ℕ) < x.queryLog.length := by
    by_contra hge
    push Not at hge
    have hnone : x.queryLog[(↑s : ℕ)]? = none := List.getElem?_eq_none hge
    rw [hnone] at htarget
    exact (Option.some_ne_none x.target htarget.symm).elim
  obtain ⟨ω, hcache_idx, hlog⟩ :=
    Fork.runTrace_cache_outer_lockstep σ hr M nmaAdv pk h (↑s : ℕ) hslt
  have htgt_eq : x.queryLog[(↑s : ℕ)]'hslt = x.target := by
    have h1 : x.queryLog[(↑s : ℕ)]? = some (x.queryLog[(↑s : ℕ)]'hslt) :=
      List.getElem?_eq_getElem hslt
    rw [h1] at htarget
    exact Option.some.inj htarget
  rw [htgt_eq] at hcache_idx
  obtain ⟨ω', hcache', hverify⟩ :=
    Fork.runTrace_verified_imp_verify σ hr M nmaAdv pk h hverified
  have hωeq : ω = ω' := by
    rw [hcache_idx] at hcache'
    exact Option.some.inj hcache'
  refine ⟨ω, hlog, hcache_idx, ?_⟩
  rw [hωeq]
  exact hverify

omit [SampleableType Stmt] [SampleableType Wit] [Fintype Chal] [Inhabited Chal] in
/-- **Target equality across two successful fork runs** sharing the same fork index.

If both runs of `forkReplay (Fork.runTrace σ hr M nmaAdv pk)` select fork point `s`,
their forgery targets agree. The two runs share all counted-oracle responses strictly
before the fork index, and the replay-determinism lemma `Fork.runTrace_queryLog_take_eq`
then forces their internal `queryLog`s to coincide on the first `s + 1` entries, so
`forkPoint_getElem?_eq_some_target` pins both targets to the same value. -/
private theorem target_eq_of_mem_forkReplay
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    (x₁ x₂ : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (s : Fin (qH + 1))
    (hsup : some (x₁, x₂) ∈ support (forkReplay (Fork.runTrace σ hr M nmaAdv pk)
      (nmaForkBudget qH) (Sum.inr ())
      (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)))
    (h₁ : Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH x₁ = some s)
    (h₂ : Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH x₂ = some s) :
    x₁.target = x₂.target := by
  classical
  -- Unpack the replay-fork success structure.
  obtain ⟨log₁, log₂, s', hx₁, hx₂, hcf₁, hcf₂, _hneq, replacement, st, hz, hlog₂, _hmismatch,
    hfork, _hprefix⟩ := forkReplay_success_log_props
      (main := Fork.runTrace σ hr M nmaAdv pk)
      (qb := nmaForkBudget qH) (i := Sum.inr ())
      (cf := Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)
      hsup
  -- `s = s'` via `hcf₁` and `h₁`.
  have hs_eq : s' = s := by rw [hcf₁] at h₁; exact Option.some.inj h₁
  cases hs_eq
  -- Abbreviations for readability.
  set main : OracleComp (Fork.wrappedSpec Chal)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    Fork.runTrace σ hr M nmaAdv pk
  -- Immutable replay parameters.
  have htrace_eq : st.trace = log₁ :=
    replayRunWithTraceValue_trace_eq
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
  have hforkq : st.forkQuery = (↑s : ℕ) :=
    replayRunWithTraceValue_forkQuery_eq
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
  -- Key facts about `st.cursor`.
  obtain ⟨hcur_pos, htrace_in, hobs_in⟩ :=
    replayRunWithTraceValue_forkConsumed_imp_last_input
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz hfork
  change 0 < st.cursor at hcur_pos
  change QueryLog.inputAt? st.trace (st.cursor - 1) = some (Sum.inr ()) at htrace_in
  change QueryLog.inputAt? st.observed (st.cursor - 1) = some (Sum.inr ()) at hobs_in
  rw [htrace_eq] at htrace_in
  rw [hlog₂] at hobs_in
  have hInv := replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := Sum.inr ())
    (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
  have hcur_trace : st.cursor ≤ log₁.length := by rw [← htrace_eq]; exact hInv.1
  have hcur_obs : st.cursor ≤ log₂.length := by rw [← hlog₂]; exact hInv.2.1
  have hc1_lt_t : st.cursor - 1 < log₁.length := by omega
  have hc1_lt_o : st.cursor - 1 < log₂.length := by omega
  -- Count identity: `(log₂.take (c-1)).getQ (· = Sum.inr ()).length = s`.
  have hcount_obs :=
    replayRunWithTraceValue_forkConsumed_imp_prefix_count
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz hfork
  change (QueryLog.getQ (st.observed.take (st.cursor - 1))
    (· = Sum.inr ())).length = st.forkQuery at hcount_obs
  rw [hforkq, hlog₂] at hcount_obs
  -- Value-level prefix equality `log₁.take (c-1) = log₂.take (c-1)`.
  have htake_len₁ : (log₁.take (st.cursor - 1)).length = st.cursor - 1 :=
    List.length_take_of_le (by omega)
  have htake_len₂ : (log₂.take (st.cursor - 1)).length = st.cursor - 1 :=
    List.length_take_of_le (by omega)
  have hprefix_val : log₁.take (st.cursor - 1) = log₂.take (st.cursor - 1) := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < st.cursor - 1
    · have hgetEq : st.observed[n]? = st.trace[n]? :=
        replayRunWithTraceValue_prefix_getElem?_eq
          (main := main) (i := Sum.inr ())
          (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
          (n := n) (by rw [if_pos hfork]; exact hn)
      rw [hlog₂, htrace_eq] at hgetEq
      have hn_t : n < log₁.length := by omega
      have hn_o : n < log₂.length := by omega
      have hlen₁ : n < (log₁.take (st.cursor - 1)).length := by rw [htake_len₁]; exact hn
      have hlen₂ : n < (log₂.take (st.cursor - 1)).length := by rw [htake_len₂]; exact hn
      rw [List.getElem?_eq_getElem hlen₁, List.getElem?_eq_getElem hlen₂,
        List.getElem_take, List.getElem_take,
        ← List.getElem?_eq_getElem hn_t, ← List.getElem?_eq_getElem hn_o]
      exact hgetEq.symm
    · push Not at hn
      have hlen₁ : (log₁.take (st.cursor - 1)).length ≤ n := by rw [htake_len₁]; exact hn
      have hlen₂ : (log₂.take (st.cursor - 1)).length ≤ n := by rw [htake_len₂]; exact hn
      rw [List.getElem?_eq_none hlen₁, List.getElem?_eq_none hlen₂]
  -- Extract the distinguished entries at position `c-1` as `⟨Sum.inr (), v_i⟩`.
  have hget₁ : log₁[st.cursor - 1]? = some (log₁[st.cursor - 1]'hc1_lt_t) :=
    List.getElem?_eq_getElem hc1_lt_t
  have hget₂ : log₂[st.cursor - 1]? = some (log₂[st.cursor - 1]'hc1_lt_o) :=
    List.getElem?_eq_getElem hc1_lt_o
  have hfst₁ : (log₁[st.cursor - 1]'hc1_lt_t).1 = Sum.inr () := by
    have := htrace_in
    unfold QueryLog.inputAt? at this
    rw [hget₁] at this
    simpa using this
  have hfst₂ : (log₂[st.cursor - 1]'hc1_lt_o).1 = Sum.inr () := by
    have := hobs_in
    unfold QueryLog.inputAt? at this
    rw [hget₂] at this
    simpa using this
  -- Destructure `log_i[c-1]` as `⟨Sum.inr (), v_i⟩` for some `v_i : Chal`.
  obtain ⟨v₁, hv₁⟩ : ∃ v : Chal, log₁[st.cursor - 1]'hc1_lt_t =
      (⟨Sum.inr (), v⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) := by
    rcases hsig : log₁[st.cursor - 1]'hc1_lt_t with ⟨i, v⟩
    rw [hsig] at hfst₁
    cases i with
    | inl n => cases hfst₁
    | inr u => cases u; exact ⟨v, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Chal, log₂[st.cursor - 1]'hc1_lt_o =
      (⟨Sum.inr (), v⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) := by
    rcases hsig : log₂[st.cursor - 1]'hc1_lt_o with ⟨i, v⟩
    rw [hsig] at hfst₂
    cases i with
    | inl n => cases hfst₂
    | inr u => cases u; exact ⟨v, rfl⟩
  -- `c - 1 + 1 = c` using `0 < c`.
  have hcsub : st.cursor - 1 + 1 = st.cursor := by omega
  -- Decompose `log_i = log_i.take (c-1) ++ ⟨Sum.inr (), v_i⟩ :: log_i.drop c`.
  have hdec₁ : log₁ = log₁.take (st.cursor - 1) ++
      ((⟨Sum.inr (), v₁⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
        log₁.drop st.cursor) := by
    have hdrop :
        log₁.drop (st.cursor - 1) =
          (log₁[st.cursor - 1]'hc1_lt_t) :: log₁.drop (st.cursor - 1 + 1) :=
      List.drop_eq_getElem_cons hc1_lt_t
    rw [hcsub] at hdrop
    rw [hv₁] at hdrop
    calc log₁ = log₁.take (st.cursor - 1) ++ log₁.drop (st.cursor - 1) :=
        (List.take_append_drop _ _).symm
      _ = log₁.take (st.cursor - 1) ++
          ((⟨Sum.inr (), v₁⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
            log₁.drop st.cursor) := by rw [hdrop]
  have hdec₂ : log₂ = log₁.take (st.cursor - 1) ++
      ((⟨Sum.inr (), v₂⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
        log₂.drop st.cursor) := by
    have hdrop :
        log₂.drop (st.cursor - 1) =
          (log₂[st.cursor - 1]'hc1_lt_o) :: log₂.drop (st.cursor - 1 + 1) :=
      List.drop_eq_getElem_cons hc1_lt_o
    rw [hcsub] at hdrop
    rw [hv₂] at hdrop
    calc log₂ = log₂.take (st.cursor - 1) ++ log₂.drop (st.cursor - 1) :=
        (List.take_append_drop _ _).symm
      _ = log₁.take (st.cursor - 1) ++ log₂.drop (st.cursor - 1) := by rw [hprefix_val]
      _ = log₁.take (st.cursor - 1) ++
          ((⟨Sum.inr (), v₂⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
            log₂.drop st.cursor) := by rw [hdrop]
  -- Count: the common prefix `p = log₁.take (c-1)` has exactly `s` `Sum.inr ()` entries.
  have hpref_count :
      QueryLog.countQ (log₁.take (st.cursor - 1)) (· = Sum.inr ()) = (↑s : ℕ) := by
    unfold QueryLog.countQ
    rw [hprefix_val]
    exact hcount_obs
  -- Apply `runTrace_queryLog_take_eq` to get `x₁.queryLog.take (s+1) = x₂.queryLog.take (s+1)`.
  have htakeEq :
      x₁.queryLog.take (QueryLog.countQ (log₁.take (st.cursor - 1)) (· = Sum.inr ()) + 1) =
        x₂.queryLog.take
          (QueryLog.countQ (log₁.take (st.cursor - 1)) (· = Sum.inr ()) + 1) :=
    Fork.runTrace_queryLog_take_eq σ hr M (Resp := Resp) nmaAdv pk
      (x₁ := x₁) (x₂ := x₂) (outerLog₁ := log₁) (outerLog₂ := log₂) hx₁ hx₂
      (p := log₁.take (st.cursor - 1)) (v₁ := v₁) (v₂ := v₂)
      (rest₁ := log₁.drop st.cursor) (rest₂ := log₂.drop st.cursor) hdec₁ hdec₂
  rw [hpref_count] at htakeEq
  -- Both sides yield `x_i.queryLog[s]? = some x_i.target`; thus targets agree.
  have htgt₁ : x₁.queryLog[(↑s : ℕ)]? = some x₁.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) h₁
  have htgt₂ : x₂.queryLog[(↑s : ℕ)]? = some x₂.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) h₂
  have hs_lt₁ : (↑s : ℕ) < x₁.queryLog.length := by
    by_contra hge
    push Not at hge
    rw [List.getElem?_eq_none hge] at htgt₁
    exact (Option.some_ne_none _ htgt₁.symm).elim
  have hs_lt₂ : (↑s : ℕ) < x₂.queryLog.length := by
    by_contra hge
    push Not at hge
    rw [List.getElem?_eq_none hge] at htgt₂
    exact (Option.some_ne_none _ htgt₂.symm).elim
  have hgetElem_take :
      ∀ l : List (M × Commit),
        (l.take ((↑s : ℕ) + 1))[(↑s : ℕ)]? = l[(↑s : ℕ)]? := fun l => by
    rw [List.getElem?_take]
    split_ifs with h; · rfl
    · exact absurd (Nat.lt_succ_self _) h
  have : some x₁.target = some x₂.target := by
    rw [← htgt₁, ← htgt₂, ← hgetElem_take x₁.queryLog, ← hgetElem_take x₂.queryLog, htakeEq]
  exact Option.some.inj this

omit [SampleableType Stmt] in
/-- **Per-pk extraction bound.** Given the structural forking event on `pk` (two fork
runs selecting the same index, with distinct counted-oracle responses, both satisfying
`forkSupportInvariant`), the NMA reduction recovers a valid witness with probability at
least that of the fork event under `forkReplay`. Composes `target_eq_of_mem_forkReplay`
with special soundness. -/
private theorem perPk_extraction_bound
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    (pk : Stmt) :
    Pr[ fun r : Option
        (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
          Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
        ∃ (x₁ x₂ :
            Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
          (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
          r = some (x₁, x₂) ∧
          Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH x₁ = some s ∧
          Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH x₂ = some s ∧
          QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
            QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
          forkSupportInvariant σ M qH pk x₁ log₁ ∧
          forkSupportInvariant σ M qH pk x₂ log₂
        | forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
          (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH)] ≤
      Pr[ fun w : Wit => rel pk w = true | eufNmaReduction σ hr M nmaAdv qH pk] := by
  classical
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  let wrappedMain : OracleComp (unifSpec + chalSpec)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    Fork.runTrace σ hr M nmaAdv pk
  let cf : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      Option (Fin (qH + 1)) :=
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  let qb : ℕ ⊕ Unit → ℕ := nmaForkBudget qH
  -- Strip the simulator: `eufNmaReduction pk = simulateQ _ (eufNmaForkExtract pk)`.
  rw [show Pr[fun w : Wit => rel pk w = true | eufNmaReduction σ hr M nmaAdv qH pk] =
        Pr[fun w : Wit => rel pk w = true | eufNmaForkExtract σ hr M nmaAdv qH pk] by
      unfold eufNmaReduction
      exact probEvent_simulateQ_unifChalImpl _ _]
  -- Expand `eufNmaForkExtract pk` as a bind over `forkReplay` followed by a
  -- case-matching extractor `branchFn`.
  set branchFn : Option
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
        Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) →
      OracleComp (unifSpec + chalSpec) Wit :=
    fun result => match result with
    | none => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    | some (x₁, x₂) =>
      let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
      let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
      if _hc : c₁ = c₂ then
        match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
        | some ω₁, some ω₂ =>
            if _hω : ω₁ ≠ ω₂ then
              liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + chalSpec)
            else
              liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      else
        liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    with hbranchFn_def
  have hforkExtract_eq :
      eufNmaForkExtract σ hr M nmaAdv qH pk =
        forkReplay wrappedMain qb (Sum.inr ()) cf >>= branchFn := by
    unfold eufNmaForkExtract
    rfl
  rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  -- Pointwise comparison:
  -- `(if E r then Pr[= r | mx] else 0) ≤ Pr[= r | mx] * Pr[rel | branchFn r]`.
  by_cases hE :
      ∃ (x₁ x₂ : Fork.Trace
          (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
        (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
        r = some (x₁, x₂) ∧
        cf x₁ = some s ∧
        cf x₂ = some s ∧
        QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
          QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
        forkSupportInvariant σ M qH pk x₁ log₁ ∧
        forkSupportInvariant σ M qH pk x₂ log₂
  swap
  · rw [if_neg hE]; exact zero_le _
  rw [if_pos hE]
  by_cases hsupp : r ∈ support (forkReplay wrappedMain qb (Sum.inr ()) cf)
  swap
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
  obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
  obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
  obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
  -- The two cached challenges differ because the outer-log entries do.
  have hω_ne : ω₁ ≠ ω₂ := by
    intro heq
    apply hneq
    rw [hlog₁, hlog₂, heq]
  -- Targets coincide by the shared-prefix property of `forkReplay`.
  have htarget : x₁.target = x₂.target :=
    target_eq_of_mem_forkReplay σ hr M nmaAdv qH pk x₁ x₂ s (hreq ▸ hsupp) hcf₁ hcf₂
  set m₁ := x₁.forgery.1
  set c₁ := x₁.forgery.2.1
  set sr₁ := x₁.forgery.2.2
  set m₂ := x₂.forgery.1
  set c₂ := x₂.forgery.2.1
  set sr₂ := x₂.forgery.2.2
  have htgt₁ : x₁.target = (m₁, c₁) := rfl
  have htgt₂ : x₂.target = (m₂, c₂) := rfl
  have htarget_eq : (m₁, c₁) = (m₂, c₂) := by rw [← htgt₁, ← htgt₂]; exact htarget
  have hc_eq : c₁ = c₂ := (Prod.mk.inj htarget_eq).2
  have hcache₁' : x₁.roCache (m₁, c₁) = some ω₁ := hcache₁
  have hcache₂' : x₂.roCache (m₂, c₂) = some ω₂ := hcache₂
  have hverify₁' : σ.verify pk c₁ ω₁ sr₁ = true := hverify₁
  have hverify₂' : σ.verify pk c₂ ω₂ sr₂ = true := hverify₂
  have hverify₂'' : σ.verify pk c₁ ω₂ sr₂ = true := by rw [hc_eq]; exact hverify₂'
  -- Evaluate `branchFn r` to the extractor call.
  have hbranch :
      branchFn r = liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec) := by
    rw [hbranchFn_def, hreq]
    change (if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
          if _hω : ω₁ ≠ ω₂ then
            liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec)
          else
            liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    else
      liftComp ($ᵗ Wit) (unifSpec + chalSpec)) = _
    rw [dif_pos hc_eq, hcache₁', hcache₂']
    simp only [dif_pos hω_ne]
  rw [hbranch, probEvent_liftComp]
  -- Probability on the extracted branch is 1 via special soundness + no-failure.
  have hrel_one :
      Pr[fun w : Wit => rel pk w = true | σ.extract ω₁ sr₁ ω₂ sr₂] = 1 := by
    rw [probEvent_eq_one_iff]
    refine ⟨hss_nf ω₁ sr₁ ω₂ sr₂, fun w hw => ?_⟩
    exact SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk)
      hω_ne hverify₁' hverify₂'' hw
  rw [hrel_one, mul_one]

end eufNmaHelpers

omit [SampleableType Stmt] in
/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any managed-RO NMA adversary `B` making at most `qH` random-oracle queries, there
exists a witness-extraction reduction such that:

  `Adv^{fork-NMA}_{qH}(B) · (Adv^{fork-NMA}_{qH}(B) / (qH + 1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

Runs `B.main pk` twice with shared randomness up to a randomly chosen fork point, then
re-samples the oracle answer. Programmed cache entries are part of `B`'s deterministic
computation given the seed, so they are identical across both fork runs. The reduction
extracts only from fork outputs whose two forged transcripts share a commitment and whose
cached challenges are distinct. The remaining proof obligation is to show that successful
forks satisfy exactly those compatibility checks, after which special soundness applies.

Here `Adv^{fork-NMA}_{qH}(B)` is `Fork.advantage`: it counts exactly the
managed-RO executions whose forgery already verifies from challenge values present in the
adversary's managed cache or in the live hash-query log recorded by
`Fork.runTrace`. This is the precise success event that the forking lemma can
rewind.

This matches Firsov-Janku's `schnorr_koa_secure` at
[fsec/proof/Schnorr.ec:448](../../../fsec/proof/Schnorr.ec), which applies `forking_lemma_ro`
with the single-run postcondition `verify` plus the extractor correctness lemma
`extractor_corr` at [fsec/proof/Schnorr.ec:87](../../../fsec/proof/Schnorr.ec). Our version
uses `Fork.replayForkingBound` for the RO-level packaging and `_hss` for special
soundness, with `σ.extract` playing the role of EC's `extractor`.

The Jensen/Cauchy-Schwarz step that powers `Fork.replayForkingBound` rests on the two
prefix-faithfulness identities
(`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt` and
`tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt` in ReplayFork.lean). -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (_hQ : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := nmaAdv.main pk) qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      (Fork.advantage σ hr M nmaAdv qH *
          (Fork.advantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) -
            challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  classical
  refine ⟨eufNmaReduction σ hr M nmaAdv qH, ?_⟩
  set acc : Stmt → ENNReal := fun pk =>
    Pr[ fun x => (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH x).isSome | Fork.runTrace σ hr M nmaAdv pk] with hacc_def
  -- ── Step (a): rewrite `Fork.advantage` as the keygen-marginalized expectation of the
  -- per-pk fork-point success probability.
  have hAdv_eq_tsum :
      Fork.advantage σ hr M nmaAdv qH =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    change Pr[= true | Fork.exp σ hr M nmaAdv qH] = _
    unfold Fork.exp
    rw [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl,
      probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rw [probOutput_liftComp]
    congr 1
    rcases pkw with ⟨pk, sk⟩
    simp only [bind_pure_comp, probEvent_map, Function.comp_def, acc]
  -- ── Step (b): rewrite `Pr[= true | hardRelationExp]` as a keygen-marginalized sum of
  -- per-pk relation-recovery probabilities.
  have hRHS_eq_tsum :
      Pr[= true | hardRelationExp hr (eufNmaReduction σ hr M nmaAdv qH)] =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
          Pr[ fun w : Wit => rel pkw.1 w = true |
            eufNmaReduction σ hr M nmaAdv qH pkw.1] := by
    unfold hardRelationExp
    rw [← probEvent_eq_eq_probOutput]
    simp only [bind_pure_comp, probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rcases pkw with ⟨pk, sk⟩
    congr 1
    rw [probEvent_map]
    rfl
  -- ── Step (c): per-pk forking bound via `Fork.replayForkingBound` applied with the
  -- strengthened support invariant `forkSupportInvariant`.
  have hPerPk : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun r : Option
            (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            ∃ (x₁ x₂ :
                Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
              (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
              r = some (x₁, x₂) ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH x₁ = some s ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH x₂ = some s ∧
              QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
              forkSupportInvariant σ M qH pk x₁ log₁ ∧
              forkSupportInvariant σ M qH pk x₂ log₂
            | forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
              (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH)] := fun pk =>
    Fork.replayForkingBound (σ := σ) (hr := hr) (M := M) nmaAdv qH pk
      (P_out := forkSupportInvariant σ M qH pk)
      (hP := fun h => forkSupportInvariant_of_mem_replayFirstRun σ hr M nmaAdv qH pk h)
      (hreach := Fork.runTrace_forkPoint_CfReachable
        (σ := σ) (hr := hr) (M := M) nmaAdv qH pk)
  -- ── Step (d): compose (c) with `perPk_extraction_bound`, then integrate over keygen
  -- via `jensen_keygen_forking_bound`.
  have hPerPkFinal : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun w : Wit => rel pk w = true |
          eufNmaReduction σ hr M nmaAdv qH pk] := fun pk =>
    (hPerPk pk).trans (perPk_extraction_bound σ hr M nmaAdv qH hss hss_nf pk)
  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  have hinv_le : challengeSpaceInv Chal ≤ 1 := by
    unfold challengeSpaceInv
    have hcard : (1 : ENNReal) ≤ (Fintype.card Chal : ENNReal) := by
      exact_mod_cast Fintype.card_pos
    exact ENNReal.inv_le_one.2 hcard
  have hinv_ne_top : challengeSpaceInv Chal ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hinv_le
  exact jensen_keygen_forking_bound (gen := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true |
      eufNmaReduction σ hr M nmaAdv qH pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    hinv_ne_top (fun _ => probEvent_le_one) (fun pkw => hPerPkFinal pkw.1)

/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing
   `qS · ζ_zk + collisionSlack qS qH β`.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.

The combined bound is:

  `(ε - qS·ζ_zk - qS·(qS+qH)·β) ·
      ((ε - qS·ζ_zk - qS·(qS+qH)·β) / (qH+1) - 1/|Ω|)
    ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)` and `β` is the commitment predictability
(see `SigmaProtocol.simCommitPredictability`). The ENNReal subtraction truncates at zero,
so the bound is trivially satisfied when the simulation loss exceeds the advantage. -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (β : ℝ≥0∞) (hβ : SigmaProtocol.simCommitPredictability simTranscript β)
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      let eps := adv.advantage (runtime M) -
        (ENNReal.ofReal (qS * ζ_zk) + collisionSlack qS qH β)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    β hβ ζ_zk hζ_zk hhvzk adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) -
      (ENNReal.ofReal (qS * ζ_zk) + collisionSlack qS qH β) ≤
      Fork.advantage σ hr M nmaAdv qH :=
    tsub_le_iff_right.mpr (by rw [← add_assoc]; exact hAdv)
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end FiatShamir
