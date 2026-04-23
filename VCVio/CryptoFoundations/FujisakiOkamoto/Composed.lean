/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FujisakiOkamoto.UTransform

/-!
# Composed Fujisaki-Okamoto Transform

This file exposes the composed two-RO Fujisaki-Okamoto transform together with a single-RO
specialization for the `H(m)` branch.
-/


open OracleComp OracleSpec ENNReal

variable {M PK SK R C KD K KPRF : Type}

/-- The canonical two-RO Fujisaki-Okamoto family is the U-transform instantiated with a
variant-specific key-derivation input and rejection policy. -/
def FujisakiOkamoto
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K] :
    KEMScheme (OracleComp (UTransform.oracleSpec M R KD K))
      K PK ((PK × SK) × policy.FallbackState) C :=
  UTransform (m := OracleComp (UTransform.oracleSpec M R KD K)) pke kdInput policy

namespace FujisakiOkamoto

/-- The hash-oracle interface for the single-RO FO variant: one public oracle maps `(pkh pk, m)`
to both encryption coins and the shared key. -/
abbrev singleROHashOracleSpec (PKHash M R K : Type) :=
  (PKHash × M) →ₒ (R × K)

/-- The full oracle world for the single-RO FO variant, consisting of unrestricted public
randomness plus the combined `(pkh pk, m) ↦ (r, k)` random oracle. -/
abbrev singleROOracleSpec (PKHash M R K : Type) :=
  unifSpec + singleROHashOracleSpec PKHash M R K

/-- Cache state for the single lazy random oracle used by the single-RO FO variant. -/
abbrev SingleROQueryCache (PKHash M R K : Type) :=
  (singleROHashOracleSpec PKHash M R K).QueryCache

/-- Lazy single random oracle returning both coins and the derived key. -/
def singleROOracleImpl {PKHash M R K : Type}
    [DecidableEq PKHash] [DecidableEq M] [SampleableType R] [SampleableType K] :
    QueryImpl (singleROHashOracleSpec PKHash M R K)
      (StateT (SingleROQueryCache PKHash M R K) ProbComp) := fun inp => do
  let cache ← get
  match cache inp with
  | some out => return out
  | none =>
      let r ← ($ᵗ R : ProbComp R)
      let k ← ($ᵗ K : ProbComp K)
      let out : R × K := (r, k)
      set (cache.cacheQuery inp out)
      return out

/-- Single-RO FO hash world: both the encryption coins and the shared key are derived from the
same public random-oracle query on `(pkh pk, msg)`. -/
def singleROVariant
    {PKHash : Type}
    (pkh : PK → PKHash)
    [DecidableEq PKHash] [DecidableEq M] [SampleableType R] [SampleableType K] :
    Variant (singleROHashOracleSpec PKHash M R K) M PK C R K where
  QueryCache := SingleROQueryCache PKHash M R K
  initCache := ∅
  queryImpl := singleROOracleImpl (PKHash := PKHash) (M := M) (R := R) (K := K)
  deriveCoins := fun {m} [Monad m] [MonadLiftT ProbComp m]
      [HasQuery (singleROHashOracleSpec PKHash M R K) m] pk msg => do
    let out ← HasQuery.query (spec := singleROHashOracleSpec PKHash M R K) (m := m) (pkh pk, msg)
    return out.1
  deriveKey := fun {m} [Monad m] [MonadLiftT ProbComp m]
      [HasQuery (singleROHashOracleSpec PKHash M R K) m] pk msg _c => do
    let out ← HasQuery.query (spec := singleROHashOracleSpec PKHash M R K) (m := m) (pkh pk, msg)
    return out.2

/-- Single-RO specialization for the `H(m)` branch. The oracle input is `(pkh pk, m)` and the
oracle output supplies both the encryption coins and the shared key. -/
def singleRO
    {PKHash : Type}
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pkh : PK → PKHash)
    (policy : RejectionPolicy K C)
    [DecidableEq PKHash] [DecidableEq M] [DecidableEq C]
    [SampleableType M] [SampleableType R] [SampleableType K] :
    KEMScheme (OracleComp (singleROOracleSpec PKHash M R K))
      K PK ((PK × SK) × policy.FallbackState) C :=
  scheme (m := OracleComp (singleROOracleSpec PKHash M R K))
    pke (singleROVariant (PK := PK) (C := C) (R := R) (K := K) pkh) policy

/-- Runtime bundle for the canonical two-RO Fujisaki-Okamoto oracle world. -/
noncomputable def twoRORuntime
    [DecidableEq M] [DecidableEq KD]
    [SampleableType R] [SampleableType K] :
    ProbCompRuntime (OracleComp (UTransform.oracleSpec M R KD K)) :=
  UTransform.runtime (R := R) (KD := KD) (K := K)

/-- Runtime bundle for the single-RO Fujisaki-Okamoto oracle world. -/
noncomputable def singleRORuntime
    {PKHash : Type}
    [DecidableEq PKHash] [DecidableEq M] [SampleableType R] [SampleableType K] :
    ProbCompRuntime (OracleComp (singleROOracleSpec PKHash M R K)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := singleROOracleImpl (PKHash := PKHash) (M := M) (R := R) (K := K))
    (∅ : SingleROQueryCache PKHash M R K)
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Main composed Fujisaki-Okamoto IND-CCA theorem statement.

**WARNING: this is a placeholder statement, not the final theorem.** The current shape is
unsound as written: `correctnessBound` and `epsMsg` are unconstrained `ℝ` parameters, so
the right-hand side can be made arbitrarily negative while the left-hand side is a
probability and hence nonnegative. In the final composed FO statement these slack terms
must be constrained (`correctnessBound` is the underlying PKE's `δ`-correctness error, and
`epsMsg` is the message-distribution collision/min-entropy term, both provably nonnegative
quantities derived from `pke`).

The proof is intentionally deferred. The reduction artifacts (`cpaAdv₁`, `cpaAdv₂`,
`prfAdv`) are existentially quantified rather than passed in as unrelated inputs, but the
bound itself still needs to be tightened before this can be a meaningful security claim. -/
theorem IND_CCA_bound
    {M PK SK R C KD K KPRF : Type}
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (prf : PRFScheme KPRF C K)
    (adversary : (FujisakiOkamoto pke kdInput (implicitRejection prf)).IND_CCA_Adversary)
    (correctnessBound epsMsg : ℝ)
    (qHK : ℕ) :
    ∃ cpaAdv₁ cpaAdv₂ : (pke.toAsymmEncAlg ProbCompRuntime.probComp).IND_CPA_adversary,
      ∃ prfAdv : PRFScheme.PRFAdversary C K,
        (FujisakiOkamoto pke kdInput (implicitRejection prf)).IND_CCA_Advantage
            (twoRORuntime (M := M) (R := R) (KD := KD) (K := K))
            adversary ≤
          2 * ((pke.toAsymmEncAlg ProbCompRuntime.probComp).IND_CPA_advantage cpaAdv₁).toReal +
          2 * ((pke.toAsymmEncAlg ProbCompRuntime.probComp).IND_CPA_advantage cpaAdv₂).toReal +
          PRFScheme.prfAdvantage prf prfAdv +
          ((2 * qHK + 3 : ℕ) : ℝ) * correctnessBound +
          2 * ((2 * qHK + 2 : ℕ) : ℝ) * epsMsg := by
  sorry

end FujisakiOkamoto
