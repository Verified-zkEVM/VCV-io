/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.Control.Monad.Hom
public import VCVio.EvalDist.Defs.Instances
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Signature Algorithms

This file defines `SignatureAlg m M PK SK S`, a type representing a digital signature scheme
with computations in the monad `m`, message space `M`, public/secret key spaces `PK`/`SK`,
and signature space `S`.

## Main definitions

* `SignatureAlg`: a signature scheme as a `keygen`/`sign`/`verify` triple in a monad `m`.
* `SignatureAlg.Complete`: completeness up to an error `δ`, with `PerfectlyComplete` the `δ = 0`
  case.
* `SignatureAlg.unforgeableExp`, `strongUnforgeableExp`, `eufNmaExp`, `managedRoNmaExp`: the
  EUF-CMA, SUF-CMA, EUF-NMA, and managed-random-oracle NMA security experiments, with the
  corresponding adversary advantages.
-/

@[expose] public section

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

Every successful response is recorded as its exact `(message, signature)` pair in a
`WriterT (QueryLog (M →ₒ S))` writer layer. EUF-CMA projects this trace to queried messages;
SUF-CMA checks whether the exact final pair occurs in it. -/
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
  ∀ msg : M, (1 : ℝ≥0∞) - δ ≤ Pr[= true | runtime.evalSPMF do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig]

/-- Perfect completeness: the canonical keygen-sign-verify execution always accepts.
This is the special case of `Complete` with zero error. -/
def PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, Pr[= true | runtime.evalSPMF do
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
lemma le_probOutput_bind_of_forall_support {α β : Type} {a : β} {δ : ℝ≥0∞} (gen : ProbComp α)
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
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : unforgeableAdv sigAlg) :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalSPMF do
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
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : unforgeableAdv sigAlg) :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalSPMF do
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

Both `unforgeableExp` and `unforgeableExpNoFresh` factor as `runtime.evalSPMF (joint >>= ...)`
sharing the same prefix `joint`. The hypothesis `h_pull` packages the runtime-specific
factoring step that pulls a pure-returning bind out of `runtime.evalSPMF`, and is satisfied
by `withStateOracle`-style runtimes via `SPMFSemantics.withStateOracle_evalSPMF_bind_pure`
(see e.g. `FiatShamir.runtime_evalSPMF_bind_pure`). -/
lemma unforgeableAdv.advantage_le_unforgeableExpNoFresh
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : unforgeableAdv sigAlg) :
    adv.advantage runtime ≤ Pr[= true | unforgeableExpNoFresh runtime adv] := by
  let : DecidableEq M := Classical.decEq M
  let : DecidableEq S := Classical.decEq S
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
  have hExp : (runtime.evalSPMF do
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
        runtime.evalSPMF joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  have hNoFresh : (runtime.evalSPMF do
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
      (fun t : M × QueryLog (M →ₒ S) × Bool => t.2.2) <$> runtime.evalSPMF joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  rw [hExp, hNoFresh, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono fun _ _ => Bool.and_elim_right

end unforgeable

section strongUnforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

/-- Whether the signing-oracle trace contains the exact returned pair `(msg, σ)`. Unlike
`QueryLog.wasQueried`, this predicate distinguishes two signatures returned for the same message. -/
def signingLogContains (log : QueryLog (M →ₒ S)) (msg : M) (σ : S) : Bool :=
  decide (⟨msg, σ⟩ ∈ log)

@[simp]
lemma signingLogContains_nil (msg : M) (σ : S) :
    signingLogContains ([] : QueryLog (M →ₒ S)) msg σ = false := by
  simp [signingLogContains]

@[simp]
lemma signingLogContains_singleton_self (msg : M) (σ : S) :
    signingLogContains ([⟨msg, σ⟩] : QueryLog (M →ₒ S)) msg σ = true := by
  simp [signingLogContains]

/-- Exact returned-pair membership implies ordinary message membership in the same signing log. -/
lemma wasQueried_eq_true_of_signingLogContains_eq_true
    (log : QueryLog (M →ₒ S)) (msg : M) (σ : S)
    (h : signingLogContains log msg σ = true) : log.wasQueried msg = true := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq]
  rw [signingLogContains, decide_eq_true_eq] at h
  exact List.mem_map.mpr ⟨⟨msg, σ⟩, h, rfl⟩

omit [DecidableEq M] [DecidableEq S] in
/-- An `SPMF`'s compatibility measure agrees with its executable point probability on a
singleton. This is the local bridge used by the measure-valued security experiments below. -/
private lemma compatibilityMeasure_apply_singleton
    (dist : SPMF Bool) (b : Bool) : dist.toMeasure {b} = Pr[= b | dist] := by
  rw [SPMF.toMeasure_apply_singleton]
  rfl

/-- A SUF-CMA (strong unforgeability under chosen-message attack) adversary. As in EUF-CMA it
receives the public key and has access to the scheme's ambient oracles plus the signing oracle,
but its final pair is fresh when that exact `(message, signature)` pair was never returned. -/
structure strongUnforgeableAdv (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (M × S)

/-- The computation underlying strong unforgeability under chosen-message attack. The signing
oracle logs every successful returned `(message, signature)` pair. The adversary succeeds exactly
when its final pair verifies and that pair does not occur in the returned-pair log. -/
noncomputable def strongUnforgeableGame
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : strongUnforgeableAdv sigAlg) : OracleComp spec Bool :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← simAdv.run
    let verified ← sigAlg.verify pk msg σ
    return !signingLogContains log msg σ && verified

/-- The canonical measure-valued SUF-CMA experiment. The explicit `SPMF.toMeasure` application
is the compatibility boundary from the runtime's finite evaluator to VCVio's primary measure API. -/
noncomputable def strongUnforgeableExp
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : strongUnforgeableAdv sigAlg) : MeasureTheory.Measure Bool :=
  (runtime.evalSPMF (strongUnforgeableGame adv)).toMeasure

omit [DecidableEq M] [DecidableEq S] in
/-- On a singleton event, the measure-valued SUF experiment agrees with the executable
point-probability reading. -/
lemma strongUnforgeableExp_apply_singleton
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : strongUnforgeableAdv sigAlg) (b : Bool) :
    strongUnforgeableExp runtime adv {b} =
      Pr[= b | runtime.evalSPMF (strongUnforgeableGame adv)] := by
  exact compatibilityMeasure_apply_singleton
    (runtime.evalSPMF (strongUnforgeableGame adv)) b

/-- The SUF-CMA success probability: the probability of outputting a valid pair not previously
returned by the signing oracle. -/
noncomputable def strongUnforgeableAdv.advantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : strongUnforgeableAdv sigAlg) : ℝ≥0∞ :=
  strongUnforgeableExp runtime adv {true}

/-- Forget pair freshness and regard a strong-unforgeability adversary as an ordinary
EUF-CMA adversary.  The oracle interface and adversary program are unchanged. -/
def strongUnforgeableAdv.toUnforgeableAdv
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : strongUnforgeableAdv sigAlg) : unforgeableAdv sigAlg where
  main := adv.main

/-- The computation for the extra event separating SUF-CMA from EUF-CMA: the adversary returns a
valid, new signature for a message that it did submit to the signing oracle. This event is
intentionally defined without assigning it to a cryptographic assumption; doing so is
scheme-specific (for example, it may require signature binding or a rerandomization argument). -/
noncomputable def sameMessageStrongUnforgeableGame
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : strongUnforgeableAdv sigAlg) : OracleComp spec Bool :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← simAdv.run
    let verified ← sigAlg.verify pk msg σ
    return log.wasQueried msg && !signingLogContains log msg σ && verified

/-- The canonical measure-valued same-message, new-signature experiment. -/
noncomputable def sameMessageStrongUnforgeableExp
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : strongUnforgeableAdv sigAlg) : MeasureTheory.Measure Bool :=
  (runtime.evalSPMF (sameMessageStrongUnforgeableGame adv)).toMeasure

omit [DecidableEq M] [DecidableEq S] in
/-- On a singleton event, the measure-valued same-message experiment agrees with the
executable point-probability reading. -/
lemma sameMessageStrongUnforgeableExp_apply_singleton
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : strongUnforgeableAdv sigAlg) (b : Bool) :
    sameMessageStrongUnforgeableExp runtime adv {b} =
      Pr[= b | runtime.evalSPMF (sameMessageStrongUnforgeableGame adv)] := by
  exact compatibilityMeasure_apply_singleton
    (runtime.evalSPMF (sameMessageStrongUnforgeableGame adv)) b

/-- Probability of the same-message, new-signature event in the strong-unforgeability
experiment. -/
noncomputable def strongUnforgeableAdv.sameMessageAdvantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : strongUnforgeableAdv sigAlg) : ℝ≥0∞ :=
  sameMessageStrongUnforgeableExp runtime adv {true}

/-- Quantitative scheme property needed in addition to EUF-CMA for strong unforgeability: every
adversary has at most `ε` probability of returning a new valid signature for a message previously
submitted to the signing oracle.

This quantifies over *all* adversaries with no query or time bound, so it is an
information-theoretic property. It is satisfiable with small `ε` only for schemes whose valid
signatures are (statistically close to) unique per message, such as unique-signature schemes.
For schemes where an unbounded adversary can find a second valid signature — hash-based schemes
like SLH-DSA included — no `ε < 1` can hold, and quantitative results should instead consume the
per-adversary partition `strongUnforgeableAdv.advantage_eq_euf_add_sameMessage` directly,
bounding the same-message term for the specific reduction adversary at hand. -/
def SameMessageBinding (sigAlg : SignatureAlg (OracleComp spec) M PK SK S)
    (runtime : ProbCompRuntime (OracleComp spec)) (ε : ℝ≥0∞) : Prop :=
  ∀ adv : strongUnforgeableAdv sigAlg, adv.sameMessageAdvantage runtime ≤ ε

omit [DecidableEq M] [DecidableEq S] in
/-- **Exact generic SUF-to-EUF partition.** Every strong forgery either uses a message never queried
to the signing oracle (an ordinary EUF-CMA forgery) or is a new valid signature for a previously
queried message. These events are disjoint and exhaustive inside the exact-pair-fresh success
event, so SUF-CMA equals EUF-CMA plus precisely the latter, scheme-specific same-message event.

The `h_pull` hypothesis is the same runtime-factoring law used by the EUF freshness lemma above.
It is satisfied by the standard state-oracle runtimes used by VCVio. -/
lemma strongUnforgeableAdv.advantage_eq_euf_add_sameMessage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : strongUnforgeableAdv sigAlg) :
    adv.advantage runtime =
      adv.toUnforgeableAdv.advantage runtime + adv.sameMessageAdvantage runtime := by
  let : DecidableEq M := Classical.decEq M
  let : DecidableEq S := Classical.decEq S
  unfold strongUnforgeableAdv.advantage strongUnforgeableExp strongUnforgeableGame
    unforgeableAdv.advantage unforgeableExp
    strongUnforgeableAdv.sameMessageAdvantage sameMessageStrongUnforgeableExp
    sameMessageStrongUnforgeableGame
  set joint : OracleComp spec (M × S × QueryLog (M →ₒ S) × Bool) := do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← simAdv.run
    let verified ← sigAlg.verify pk msg σ
    pure (msg, σ, log, verified) with hjoint_def
  have hSuf : (runtime.evalSPMF do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.main pk)
        let ((msg, σ), log) ← simAdv.run
        let verified ← sigAlg.verify pk msg σ
        pure (!signingLogContains log msg σ && verified)) =
      (fun t : M × S × QueryLog (M →ₒ S) × Bool =>
        !signingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2) <$> runtime.evalSPMF joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  have hEuf : (runtime.evalSPMF do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.toUnforgeableAdv.main pk)
        let ((msg, σ), log) ← simAdv.run
        let verified ← sigAlg.verify pk msg σ
        pure (!log.wasQueried msg && verified)) =
      (fun t : M × S × QueryLog (M →ₒ S) × Bool =>
        !t.2.2.1.wasQueried t.1 && t.2.2.2) <$> runtime.evalSPMF joint := by
    rw [← h_pull]
    congr 1
    simp only [strongUnforgeableAdv.toUnforgeableAdv, hjoint_def, monad_norm]
  have hSame : (runtime.evalSPMF do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let simAdv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.main pk)
        let ((msg, σ), log) ← simAdv.run
        let verified ← sigAlg.verify pk msg σ
        pure (log.wasQueried msg && !signingLogContains log msg σ && verified)) =
      (fun t : M × S × QueryLog (M →ₒ S) × Bool =>
        t.2.2.1.wasQueried t.1 &&
          !signingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2) <$> runtime.evalSPMF joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  rw [hSuf, hEuf, hSame, compatibilityMeasure_apply_singleton,
    compatibilityMeasure_apply_singleton]
  change Pr[= true | (fun t : M × S × QueryLog (M →ₒ S) × Bool =>
      !signingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2) <$> runtime.evalSPMF joint] =
    Pr[= true | (fun t : M × S × QueryLog (M →ₒ S) × Bool =>
      !t.2.2.1.wasQueried t.1 && t.2.2.2) <$> runtime.evalSPMF joint] +
    Pr[= true | (fun t : M × S × QueryLog (M →ₒ S) × Bool =>
      t.2.2.1.wasQueried t.1 && !signingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2) <$>
        runtime.evalSPMF joint]
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map, probEvent_map]
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine tsum_congr fun t => ?_
  by_cases hm : t.2.2.1.wasQueried t.1 = true
  · cases hp : signingLogContains t.2.2.1 t.1 t.2.1 <;>
      cases hv : t.2.2.2 <;>
      simp only [Function.comp_apply, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, hp, hv, hm, Bool.false_eq_true, true_and, false_and,
        and_false, if_false, if_true, zero_add, add_zero]
  · cases hp : signingLogContains t.2.2.1 t.1 t.2.1
    · cases hv : t.2.2.2 <;>
        simp only [Function.comp_apply, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, hp, hv, hm, Bool.false_eq_true, true_and, false_and,
          and_false, if_false, if_true, add_zero]
    · exact (hm (wasQueried_eq_true_of_signingLogContains_eq_true
        t.2.2.1 t.1 t.2.1 hp)).elim

omit [DecidableEq M] [DecidableEq S] in
/-- Convenient inequality corollary of the exact SUF-to-EUF partition. -/
lemma strongUnforgeableAdv.advantage_le_euf_add_sameMessage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    (adv : strongUnforgeableAdv sigAlg) :
    adv.advantage runtime ≤
      adv.toUnforgeableAdv.advantage runtime + adv.sameMessageAdvantage runtime :=
  (adv.advantage_eq_euf_add_sameMessage runtime h_pull).le

omit [DecidableEq M] [DecidableEq S] in
/-- SUF-CMA from EUF-CMA plus a quantitative same-message binding property. -/
lemma strongUnforgeableAdv.advantage_le_euf_add_of_sameMessageBinding
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalSPMF (mx >>= fun x => pure (f x)) = f <$> runtime.evalSPMF mx)
    {ε : ℝ≥0∞} (hbinding : sigAlg.SameMessageBinding runtime ε)
    (adv : strongUnforgeableAdv sigAlg) :
    adv.advantage runtime ≤ adv.toUnforgeableAdv.advantage runtime + ε := by
  rw [adv.advantage_eq_euf_add_sameMessage runtime h_pull]
  exact add_le_add le_rfl (hbinding adv)

end strongUnforgeable

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
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : eufNmaAdv sigAlg) :=
  runtime.evalSPMF do
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
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : managedRoNmaAdv sigAlg) :=
  runtime.evalSPMF do
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
