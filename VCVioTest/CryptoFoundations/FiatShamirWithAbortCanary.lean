/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security

/-!
# Fiat-Shamir-with-aborts CMA-to-NMA canaries

Producer-level pins for the CMA-to-NMA engine, on a toy identification scheme whose
messages, commitments and challenges are all `Bool` and therefore distinguishable. Each
pin fixes an exact value that a specific class of silent drift in the engine would move:

* the loss `cmaToNmaLoss` at rational points chosen to separate the `1/(1-p)` retry
  amplification of the HVZK term from the other summands;
* the two-layer ghost signing body `ghostSignBody`, read on both layers at both
  commitment points, so that swapping the real and ghost layers moves every atom;
* the managed NMA reduction `simulatedNmaAdv` on a probe adversary that makes a uniform
  query, hashes one point twice, signs one message and forges on another, so that caching
  a uniform answer, forwarding a hash miss without caching, or programming the signing
  transcript at the wrong point moves the returned cache;
* the Option-B erasure of the forgery's own verification point, both on the returned cache
  of the probe and on the managed-RO NMA success of a replay adversary.

Every pin is a closed probability obtained by normalisation; nothing here is a security
statement.
-/

public section

open OracleComp OracleSpec ENNReal FiatShamirWithAbort

namespace VCVioTest.FiatShamirWithAbortCanary

/-! ## The toy identification scheme -/

/-- Toy identification scheme over `Bool`: the commitment is a uniform bit, the prover
aborts exactly when the challenge is `false` and otherwise responds with `true`, and
verification accepts exactly when the response equals the challenge. Honest transcripts are
`(w, true, true)` for a uniform `w`, each attempt aborts with probability `1/2`, and a
transcript re-verified against a fresh challenge is accepted with probability `1/2`. -/
def toyIds : IdenSchemeWithAbort Unit Unit Bool Unit Bool Bool (fun _ _ => true) where
  commit _ _ := (fun w => (w, ())) <$> ($ᵗ Bool)
  respond _ _ _ c := pure (if c = true then some true else none)
  verify _ _ c z := decide (z = c)

/-- The trivial key relation on `Unit`. -/
def toyHr : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((), ())
  gen_sound _ _ _ := rfl

/-- The exact simulator of `toyIds`'s honest transcripts. -/
def toySim : Unit → ProbComp (Option (Bool × Bool × Bool)) := fun _ => do
  let w ← $ᵗ Bool
  let c ← $ᵗ Bool
  pure (if c = true then some (w, c, true) else none)

/-! ## Loss drift

`cmaToNmaLoss qS qH ε p ζ_zk δ = 2·qS·(qH+1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk/(1-p) + δ`.
-/

/-- At `qS = qH = 1`, `ε = 1/4`, `p = 1/2`, `ζ_zk = 1/8`, `δ = 1/16` the four summands are
`2`, `1`, `1/4` and `1/16`. Without the retry amplification on the HVZK term the third
summand would be `1/8` and the total `51/16`. -/
theorem cmaToNmaLoss_pin₁ :
    cmaToNmaLoss 1 1 (1 / 4) (1 / 2) (1 / 8) (1 / 16) (by norm_num) = 53 / 16 := by
  norm_num [cmaToNmaLoss]

/-- At `qS = 2`, `qH = 3`, `ε = 1/8`, `p = 1/2`, `ζ_zk = 1/4`, `δ = 1/16` the summands are
`4`, `3/2`, `1` and `1/16`. -/
theorem cmaToNmaLoss_pin₂ :
    cmaToNmaLoss 2 3 (1 / 8) (1 / 2) (1 / 4) (1 / 16) (by norm_num) = 105 / 16 := by
  norm_num [cmaToNmaLoss]

/-- Without aborts (`p = 0`) and with no bad keys, the HVZK term is bare `qS·ζ_zk`. -/
theorem cmaToNmaLoss_pin₃ :
    cmaToNmaLoss 1 0 (1 / 4) 0 (1 / 8) 0 (by norm_num) = 7 / 8 := by
  norm_num [cmaToNmaLoss]

/-! ## Base/ghost layer separation -/

/-- Read a two-layer cache at both commitment points of the message `true`: the real layer
first, then the ghost layer. -/
def layerView
    (s : (Bool × Bool →ₒ Bool).QueryCache × (Bool × Bool →ₒ Bool).QueryCache) :
    (Option Bool × Option Bool) × (Option Bool × Option Bool) :=
  ((s.1 (true, true), s.1 (true, false)), (s.2 (true, true), s.2 (true, false)))

/-- Two attempts of the ghost signing body on the message `true`, from empty layers, observed
through the signing output and `layerView`. -/
noncomputable def ghostRun :
    ProbComp (Option (Bool × Bool) × ((Option Bool × Option Bool) × (Option Bool × Option Bool))) :=
  (fun zs => (zs.1, layerView zs.2)) <$> (ghostSignBody toyIds Bool () () true 2).run (∅, ∅)

/-- Both attempts abort with distinct commitments (probability `1/2 · 1/2 · 1/2`): the real
layer is empty and the ghost layer holds both rejected programmings. -/
theorem ghostRun_pin_abort_abort :
    Pr[= (none, ((none, none), (some false, some false))) | ghostRun] = 1 / 8 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp [ghostRun, ghostSignBody, layerView, toyIds, StateT.run_bind, StateT.run_map,
    StateT.run_modify, probOutput_bind_eq_tsum, uncacheQuery, QueryCache.cacheQuery,
    Finset.filter_insert, Finset.filter_singleton]
  simp (disch := finiteness) [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- The first attempt aborts at commitment `false` and the second succeeds at commitment
`true` (probability `1/16`): the real layer holds the accepted programming at `(true, true)`
and the ghost layer keeps the rejected one at `(true, false)`. -/
theorem ghostRun_pin_abort_accept :
    Pr[= (some (true, true), ((some true, none), (none, some false))) | ghostRun] = 1 / 16 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp [ghostRun, ghostSignBody, layerView, toyIds, StateT.run_bind, StateT.run_map,
    StateT.run_modify, probOutput_bind_eq_tsum, uncacheQuery, QueryCache.cacheQuery,
    Finset.filter_insert, Finset.filter_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- An accepted signature at commitment `true` with an empty ghost layer: either the first
attempt succeeds there (`1/4`), or the first aborts there and the second succeeds there, in
which case the accepted programming uncaches the ghost entry (`1/16`). -/
theorem ghostRun_pin_accept_clean :
    Pr[= (some (true, true), ((some true, none), (none, none))) | ghostRun] = 5 / 16 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp [ghostRun, ghostSignBody, layerView, toyIds, StateT.run_bind, StateT.run_map,
    StateT.run_modify, probOutput_bind_eq_tsum, uncacheQuery, QueryCache.cacheQuery,
    Finset.filter_insert, Finset.filter_singleton]
  simp (disch := finiteness) [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-! ## Managed cache bookkeeping and forgery-point erasure -/

/-- The toy scheme's ambient oracle family: uniform selection plus the random oracle on
`(message, commitment)` pairs. -/
abbrev toySpec := unifSpec + (Bool × Bool →ₒ Bool)

/-- The oracle family seen by a CMA adversary against the toy scheme: `toySpec` plus the
signing oracle. -/
abbrev advSpec := toySpec + (Bool →ₒ Option (Bool × Bool))

/-- The toy scheme as a signature scheme with a single signing attempt. -/
abbrev toySig := FiatShamirWithAbort (m := OracleComp toySpec) toyIds toyHr Bool 1

/-- The probe adversary: one uniform query, the same hash point twice, one signature on the
message `false`, and a forgery on the message `true` whose bit records whether the two hash
answers agreed. -/
def probeAdv : SignatureAlg.unforgeableAdv toySig where
  main _ := do
    let _ ← advSpec.query (.inl (.inl 1))
    let h₁ ← advSpec.query (.inl (.inr (true, false)))
    let h₂ ← advSpec.query (.inl (.inr (true, false)))
    let σ ← advSpec.query (.inr false)
    pure (decide (h₁ = h₂), σ)

/-- What the probe observes: the forgery, and the managed cache read at the uniform point `1`
and at the four `(message, commitment)` points. -/
structure ProbeView where
  /-- The forged message. -/
  msg : Bool
  /-- The forged signature. -/
  sig : Option (Bool × Bool)
  /-- The cache at the uniform point `1`. -/
  unif : Option (Fin 2)
  /-- The cache at `(false, true)`. -/
  ft : Option Bool
  /-- The cache at `(false, false)`. -/
  ff : Option Bool
  /-- The cache at `(true, true)`. -/
  tt : Option Bool
  /-- The cache at `(true, false)`. -/
  tf : Option Bool
  deriving DecidableEq

/-- Observe a forgery and a managed cache as a `ProbeView`. -/
def probeView (r : (Bool × Option (Bool × Bool)) × toySpec.QueryCache) : ProbeView where
  msg := r.1.1
  sig := r.1.2
  unif := r.2 (Sum.inl 1)
  ft := r.2 (Sum.inr (false, true))
  ff := r.2 (Sum.inr (false, false))
  tt := r.2 (Sum.inr (true, true))
  tf := r.2 (Sum.inr (true, false))

/-- The managed NMA reduction on the probe, run to completion under the live random oracle
and observed through `probeView`. -/
noncomputable def probeRun : ProbComp ProbeView :=
  StateT.run'
    (simulateQ
      (unifFwdImpl (Bool × Bool →ₒ Bool) +
        (randomOracle : QueryImpl (Bool × Bool →ₒ Bool)
          (StateT (Bool × Bool →ₒ Bool).QueryCache ProbComp)))
      (probeView <$>
        (simulatedNmaAdv toyIds toyHr Bool 1 toySim probeAdv).main ()))
    ∅

/-- The simulator aborts (probability `1/2`) and the live hash answer is `true` (`1/2`): no
signature, the forgery message is `true` because both hash answers agree, the uniform point
is not cached, nothing is programmed, and the live read at `(true, false)` is cached. -/
theorem probeRun_pin_abort :
    Pr[= ⟨true, none, none, none, none, none, some true⟩ | probeRun] = 1 / 4 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp only [probeRun, simulatedNmaAdv, probeAdv, toySim, toyIds, firstSome, simulateQ_bind,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind,
    StateT.run_get, map_eq_bind_pure_comp, bind_assoc, pure_bind, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, simulateQ_unifSim_run, roSim.simulateQ_liftComp]
  simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
    OracleComp.liftM_run_StateT, randomOracle, bind_assoc, QueryCache.cacheQuery, simulateQ_bind]
  simp [probeView, QueryImpl.simulateQ_toQueryImpl, probOutput_bind_eq_tsum, probOutput_query,
    QueryCache.cacheQuery]
  norm_num

/-- The simulator accepts at commitment `true` (`1/4`) and the live hash answer is `false`
(`1/2`): the transcript is programmed at `(false, true)`, and the forgery point `(true, true)`
is distinct from the cached live read at `(true, false)`, which survives. -/
theorem probeRun_pin_sign_true :
    Pr[= ⟨true, some (true, true), none, some true, none, none, some false⟩ | probeRun]
      = 1 / 8 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp only [probeRun, simulatedNmaAdv, probeAdv, toySim, toyIds, firstSome, simulateQ_bind,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind,
    StateT.run_get, map_eq_bind_pure_comp, bind_assoc, pure_bind, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, simulateQ_unifSim_run, roSim.simulateQ_liftComp]
  simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
    OracleComp.liftM_run_StateT, randomOracle, bind_assoc, QueryCache.cacheQuery, simulateQ_bind]
  simp (config := { decide := true }) [probeView, QueryImpl.simulateQ_toQueryImpl,
    probOutput_bind_eq_tsum, probOutput_query, QueryCache.cacheQuery, Fintype.sum_prod_type,
    Finset.filter_insert, Finset.filter_singleton]
  norm_num

/-- The simulator accepts at commitment `false` (`1/4`): the transcript is programmed at
`(false, false)`, and the forgery point `(true, false)` coincides with the cached live read,
which Option B erases regardless of the live answer. -/
theorem probeRun_pin_sign_false_erases :
    Pr[= ⟨true, some (false, true), none, none, some true, none, none⟩ | probeRun]
      = 1 / 4 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp only [probeRun, simulatedNmaAdv, probeAdv, toySim, toyIds, firstSome, simulateQ_bind,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind,
    StateT.run_get, map_eq_bind_pure_comp, bind_assoc, pure_bind, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, simulateQ_unifSim_run, roSim.simulateQ_liftComp]
  simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
    OracleComp.liftM_run_StateT, randomOracle, bind_assoc, QueryCache.cacheQuery, simulateQ_bind]
  simp (config := { decide := true }) [probeView, QueryImpl.simulateQ_toQueryImpl,
    probOutput_bind_eq_tsum, probOutput_query, QueryCache.cacheQuery, Fintype.sum_prod_type,
    Finset.filter_insert, Finset.filter_singleton]
  norm_num

/-- The toy runtime is the caching random oracle over the empty cache. -/
lemma runtime_evalSPMF {α : Type} (oa : OracleComp toySpec α) :
    (runtime (Commit := Bool) (Chal := Bool) Bool).evalSPMF oa =
      𝒮[(simulateQ (unifFwdImpl (Bool × Bool →ₒ Bool) +
          (randomOracle : QueryImpl (Bool × Bool →ₒ Bool)
            (StateT (Bool × Bool →ₒ Bool).QueryCache ProbComp))) oa).run' ∅] := rfl

/-- The replay adversary: request one signature on `true` and return it as the forgery. -/
def replayAdv : SignatureAlg.unforgeableAdv toySig where
  main _ := do
    let σ ← advSpec.query (.inr true)
    pure (true, σ)

/-- Managed-RO NMA success of the reduction on the replay adversary: the simulated signature
exists with probability `1/2`, and because its verification point is erased from the returned
cache, verification re-hashes it live and accepts with probability `1/2`. Without the erasure
the programmed challenge would be replayed and the value would be `1/2`. The proof goes through
the bridge `managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp`, whose own proof is what the erasure
sustains; the direct cache-level witness of the erasure is `probeRun_pin_sign_false_erases`. -/
theorem managedRoNmaExp_replay_pin :
    Pr[= true | SignatureAlg.managedRoNmaExp (runtime (Commit := Bool) (Chal := Bool) Bool)
      (simulatedNmaAdv toyIds toyHr Bool 1 toySim replayAdv)] = 1 / 4 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  rw [managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp]
  simp only [SignatureAlg.eufNmaExp, simulatedEufNmaAdv, runtime_evalSPMF, probOutput_evalSPMF,
    simulatedNmaAdv, replayAdv, toySim, toyIds, toyHr, firstSome, FiatShamirWithAbort,
    simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    StateT.run_bind, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    QueryImpl.add_apply_inr, simulateQ_unifSim_run, roSim.simulateQ_liftComp]
  simp only [randomOracle, QueryCache.cacheQuery]
  simp (config := { decide := true }) [unifFwdImpl.simulateQ_run, roSim.simulateQ_liftM_spec_query,
    StateT.run_bind, StateT.run_modifyGet, StateT.run_pure, map_eq_bind_pure_comp,
    probOutput_bind_eq_tsum, Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton,
    apply_ite Finset.card, Finset.card_singleton, Finset.card_empty, Finset.sum_ite_eq']
  simp (disch := finiteness) [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- The same value on the plain EUF-NMA side of the bridge. -/
theorem eufNmaExp_replay_pin :
    Pr[= true | SignatureAlg.eufNmaExp (runtime (Commit := Bool) (Chal := Bool) Bool)
      (simulatedEufNmaAdv toyIds toyHr Bool 1 toySim replayAdv)] = 1 / 4 := by
  refine (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top (by finiteness)).mp ?_
  simp only [SignatureAlg.eufNmaExp, simulatedEufNmaAdv, runtime_evalSPMF, probOutput_evalSPMF,
    simulatedNmaAdv, replayAdv, toySim, toyIds, toyHr, firstSome, FiatShamirWithAbort,
    simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    StateT.run_bind, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    QueryImpl.add_apply_inr, simulateQ_unifSim_run, roSim.simulateQ_liftComp]
  simp only [randomOracle, QueryCache.cacheQuery]
  simp (config := { decide := true }) [unifFwdImpl.simulateQ_run, roSim.simulateQ_liftM_spec_query,
    StateT.run_bind, StateT.run_modifyGet, StateT.run_pure, map_eq_bind_pure_comp,
    probOutput_bind_eq_tsum, Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton,
    apply_ite Finset.card, Finset.card_singleton, Finset.card_empty, Finset.sum_ite_eq']
  simp (disch := finiteness) [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

end VCVioTest.FiatShamirWithAbortCanary
