/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import PolyFun.Control.Monad.Hom
import VCVio.EvalDist.Defs.Instances
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Signature Algorithms

This file defines `SignatureAlg m M PK SK S`, a type representing a digital signature scheme
with computations in the monad `m`, message space `M`, public/secret key spaces `PK`/`SK`,
and signature space `S`.

## Main definitions

* `SignatureAlg`: a signature scheme as a `keygen`/`sign`/`verify` triple in a monad `m`.
* `SignatureAlg.Complete`: completeness up to an error `δ`, with `PerfectlyComplete` the `δ = 0`
  case.
* `SignatureAlg.unforgeableExp`, `eufNmaExp`, `managedRoNmaExp`: the EUF-CMA, EUF-NMA, and
  managed-random-oracle NMA security experiments, with the corresponding adversary advantages.
-/

universe u v

open OracleSpec OracleComp ENNReal

/-- Signature algorithm with computations in the monad `m`,
where `M` is the space of messages, `PK`/`SK` are the spaces of the public/private keys,
and `S` is the type of the final signature. -/
@[ext]
structure SignatureAlg (m : Type → Type v) [Monad m] (M PK SK S : Type) where
  keygen : m (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : m S
  verify (pk : PK) (msg : M) (σ : S) : m Bool

namespace SignatureAlg

section signingOracle

variable {m : Type → Type v} [Monad m] {M PK SK S : Type}

/-- The signing oracle for `sigAlg` under public key `pk` and secret key `sk`: the
`QueryImpl` that answers each queried message by running `sigAlg.sign pk sk` on it.

Every produced signature is recorded in a `WriterT (QueryLog (M →ₒ S))` writer layer, so an
experiment running an adversary against this oracle can later read off which messages were
signed and check the freshness of a forged message. -/
def signingOracle (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) :
    QueryImpl (M →ₒ S) (WriterT (QueryLog (M →ₒ S)) m) :=
  QueryImpl.withLogging (sigAlg.sign pk sk)

end signingOracle

section map

variable {m : Type → Type v} [Monad m] {n : Type → Type u} [Monad n]
  {M PK SK S : Type}

/-- Transport a signature scheme across a monad morphism by mapping each algorithmic component.

This is the basic reindexing operation used by naturality theorems for generic constructions:
if a signature scheme was defined in a source monad `m`, then any monad morphism `m →ᵐ n`
induces the corresponding scheme in `n`. -/
def map (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) : SignatureAlg n M PK SK S where
  keygen := F sigAlg.keygen
  sign pk sk msg := F (sigAlg.sign pk sk msg)
  verify pk msg σ := F (sigAlg.verify pk msg σ)

@[simp]
lemma map_keygen (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) :
    (sigAlg.map F).keygen = F sigAlg.keygen := rfl

@[simp]
lemma map_sign (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) (msg : M) :
    (sigAlg.map F).sign pk sk msg = F (sigAlg.sign pk sk msg) := rfl

@[simp]
lemma map_verify (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (msg : M) (σ : S) :
    (sigAlg.map F).verify pk msg σ = F (sigAlg.verify pk msg σ) := rfl

end map

section correctness

variable {m : Type → Type v} [Monad m] {M PK SK S : Type}

/-- Completeness of a signature scheme with error `δ`: for every message, the canonical
keygen-sign-verify execution accepts with probability at least `1 - δ`.

The error `δ` captures all sources of failure, including both verification mismatches and
signing failures (e.g., abort in schemes like Fiat-Shamir with aborts).

`Complete sigAlg runtime 0` is equivalent to `PerfectlyComplete sigAlg runtime`. -/
def Complete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ msg : M, (1 : ℝ≥0∞) - δ ≤ Pr[= true | runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig]

/-- Perfect completeness: the canonical keygen-sign-verify execution always accepts.
This is the special case of `Complete` with zero error. -/
def PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, Pr[= true | runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig] = 1

lemma perfectlyComplete_iff_complete_zero (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) :
    sigAlg.PerfectlyComplete runtime ↔ sigAlg.Complete runtime 0 := by
  simp [PerfectlyComplete, Complete]

lemma Complete.mono {sigAlg : SignatureAlg m M PK SK S} {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : sigAlg.Complete runtime δ₁) (hle : δ₁ ≤ δ₂) : sigAlg.Complete runtime δ₂ :=
  fun msg => (tsub_le_tsub_left hle _).trans (h msg)

/-- If every value `x` in the support of `gen` satisfies `Pr[= a | f x] ≥ 1 - δ`, then the
overall probability satisfies `Pr[= a | gen >>= f] ≥ 1 - δ`. This reduces a "for all keys"
completeness statement to per-key bounds. -/
lemma probOutput_bind_ge_of_forall_support {α β : Type} {a : β} {δ : ℝ≥0∞} (gen : ProbComp α)
    (f : α → ProbComp β) (h : ∀ x, x ∈ support gen → 1 - δ ≤ Pr[= a | f x]) :
    1 - δ ≤ Pr[= a | gen >>= f] := by
  rw [probOutput_bind_eq_tsum]
  calc 1 - δ = ∑' x, Pr[= x | gen] * (1 - δ) := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
    _ ≤ ∑' x, Pr[= x | gen] * Pr[= a | f x] := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support gen
        · gcongr; exact h x hx
        · simp [probOutput_eq_zero_of_not_mem_support hx]

end correctness

section unforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

/-- An EUF-CMA (existential unforgeability under chosen-message attack) adversary for
`sigAlg`. Given the public key, it runs in the oracle family `spec + (M →ₒ S)` — the
scheme's ambient oracles together with a signing oracle — and outputs a candidate forgery
`(message, signature)`.

The `_sigAlg` parameter indexes the adversary by a specific scheme's types but is not stored. -/
structure unforgeableAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (M × S)

/-- Unforgeability experiment for a signature algorithm: runs the adversary and checks whether
the adversary successfully forged a signature. The ambient oracle family is forwarded unchanged,
the signing oracle is logged, and the final check requires both signature validity and that the
forged message was never submitted to the signing oracle. -/
noncomputable def unforgeableExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : unforgeableAdv sigAlg) : SPMF Bool :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ
    return !log.wasQueried msg && verified

/-- The success probability of a CMA adversary in the unforgeability experiment. -/
noncomputable def unforgeableAdv.advantage {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : unforgeableAdv sigAlg) : ℝ≥0∞ := Pr[= true | unforgeableExp runtime adv]

/-- The CMA experiment with the freshness check dropped: the same body as `unforgeableExp`
but the final return is just the `verified` bit, ignoring whether the forged message was
queried by the adversary to the signing oracle.

Without the freshness check, an adversary trivially wins by replaying any received
signature; the bound `adv.advantage ≤ Pr[unforgeableExpNoFresh ⇒ true]` (see
`unforgeableAdv.advantage_le_unforgeableExpNoFresh`) is the first game-hop
in standard CMA-to-NMA reductions. -/
noncomputable def unforgeableExpNoFresh {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : unforgeableAdv sigAlg) : SPMF Bool :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), _) ← sim_adv.run
    sigAlg.verify pk msg σ

omit [DecidableEq M] [DecidableEq S] in
/-- **Phase B (freshness-drop) bound.** The CMA advantage is bounded above by the success
probability of the same experiment with the freshness check dropped.

Both `unforgeableExp` and `unforgeableExpNoFresh` factor as `runtime.evalDist (joint >>= ...)`
sharing the same prefix `joint`. The hypothesis `h_pull` packages the runtime-specific
factoring step that pulls a pure-returning bind out of `runtime.evalDist`, and is satisfied
by `withStateOracle`-style runtimes via `SPMFSemantics.withStateOracle_evalDist_bind_pure`
(see e.g. `FiatShamir.runtime_evalDist_bind_pure`). -/
lemma unforgeableAdv.advantage_le_unforgeableExpNoFresh
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalDist (mx >>= fun x => pure (f x)) = f <$> runtime.evalDist mx)
    (adv : unforgeableAdv sigAlg) :
    adv.advantage runtime ≤ Pr[= true | unforgeableExpNoFresh runtime adv] := by
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  unfold unforgeableAdv.advantage unforgeableExp unforgeableExpNoFresh
  set joint : OracleComp spec (M × QueryLog (M →ₒ S) × Bool) := do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ
    pure (msg, log, verified) with hjoint_def
  have hExp : (runtime.evalDist do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.main pk)
        let ((msg, σ), log) ← sim_adv.run
        let verified ← sigAlg.verify pk msg σ
        pure (!log.wasQueried msg && verified)) =
      (fun t : M × QueryLog (M →ₒ S) × Bool => !t.2.1.wasQueried t.1 && t.2.2) <$>
        runtime.evalDist joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  have hNoFresh : (runtime.evalDist do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.main pk)
        let ((msg, σ), _) ← sim_adv.run
        sigAlg.verify pk msg σ) =
      (fun t : M × QueryLog (M →ₒ S) × Bool => t.2.2) <$> runtime.evalDist joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  rw [hExp, hNoFresh, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono fun _ _ => Bool.and_elim_right

end unforgeable

section eufNma

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EUF-NMA (existential unforgeability under no-message attack) adversary for a
signature scheme. Unlike a CMA adversary (`unforgeableAdv`), the NMA adversary has NO
access to a signing oracle — it must forge a signature having only seen the public key.

In the random oracle model, the adversary still has access to the scheme's oracle spec
(e.g., the random oracle `H`), but never sees any legitimately generated signatures. -/
structure eufNmaAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp spec (M × S)

/-- The EUF-NMA experiment: generate a key pair, give the public key to the adversary
(with no signing oracle), and check whether the adversary produced a valid forgery. -/
def eufNmaExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : eufNmaAdv sigAlg) : SPMF Bool :=
  runtime.evalDist do
    let (pk, _) ← sigAlg.keygen
    let (msg, σ) ← adv.main pk
    sigAlg.verify pk msg σ

/-- The success probability of an EUF-NMA adversary. -/
noncomputable def eufNmaAdv.advantage {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : eufNmaAdv sigAlg) : ℝ≥0∞ := Pr[= true | eufNmaExp runtime adv]

end eufNma

section managedRoNma

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EUF-NMA adversary with managed random oracle: the adversary returns a `QueryCache`
alongside its forgery. The experiment verifies using `withCacheOverlay`, which resolves
cached entries from the adversary's table and forwards misses to the real oracle.

This supports compositional CMA-to-NMA reductions: the CMA-to-NMA reduction programs
hash entries for signing simulation into the cache, while forwarding the inner adversary's
hash queries to the external oracle. The forking lemma (`Fork.fork`) can then replay the
external oracle queries via seeded simulation, while the programmed entries are preserved
deterministically. -/
structure managedRoNmaAdv (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp spec ((M × S) × spec.QueryCache)

/-- The managed-RO NMA experiment: generate a key pair, run the adversary to get a forgery
and a `QueryCache`, then verify the forgery through `withCacheOverlay` so that programmed
entries take priority over the real oracle. -/
def managedRoNmaExp {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : managedRoNmaAdv sigAlg) : SPMF Bool :=
  runtime.evalDist do
    let (pk, _) ← sigAlg.keygen
    let ((msg, σ), cache) ← adv.main pk
    withCacheOverlay cache (sigAlg.verify pk msg σ)

/-- The success probability of a managed-RO NMA adversary. -/
noncomputable def managedRoNmaAdv.advantage {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : managedRoNmaAdv sigAlg) : ℝ≥0∞ := Pr[= true | managedRoNmaExp runtime adv]

/-- Embed a standard NMA adversary as a managed-RO NMA adversary with an empty cache.
The empty cache means all queries fall through to the real oracle, recovering the
standard NMA experiment. -/
def eufNmaAdv.toManagedRoNmaAdv {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : eufNmaAdv sigAlg) : managedRoNmaAdv sigAlg where
  main pk := (·, ∅) <$> adv.main pk

end managedRoNma

end SignatureAlg
