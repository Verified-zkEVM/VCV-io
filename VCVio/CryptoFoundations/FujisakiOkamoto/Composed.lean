import VCVio.CryptoFoundations.FujisakiOkamoto.UTransform

/-!
# Composed Fujisaki-Okamoto Transform

This file exposes the composed two-RO Fujisaki-Okamoto transform together with a single-RO
specialization for the `H(m)` branch.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

universe u v

variable {M PK SK R C KD K KPRF : Type}

/-- The generic two-RO Fujisaki-Okamoto transform is exactly the U transform instantiated on top of
the T-world derived from a deterministic explicit-coin PKE. -/
def FujisakiOkamoto
    (pke : DeterministicPKE M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (kdInput : M → C → KD)
    (rejMode : RejectionMode)
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K] :
    KEMScheme (OracleComp (UTransform.oracleSpec M R KD K))
      K PK ((PK × SK) × KPRF) C :=
  UTransform pke prf kdInput rejMode

namespace FujisakiOkamoto

abbrev singleROOracleSpec (PKHash M R K : Type) :=
  unifSpec + ((PKHash × M) →ₒ (R × K))

abbrev SingleROQueryCache (PKHash M R K : Type) :=
  ((PKHash × M) →ₒ (R × K)).QueryCache

/-- Lazy single random oracle returning both coins and the derived key. -/
def singleROOracleImpl {PKHash M R K : Type}
    [DecidableEq PKHash] [DecidableEq M] [SampleableType R] [SampleableType K] :
    QueryImpl ((PKHash × M) →ₒ (R × K))
      (StateT (SingleROQueryCache PKHash M R K) ProbComp) := fun inp => do
  let cache ← get
  match cache inp with
  | some out => return out
  | none =>
      let r ← liftM ($ᵗ R : ProbComp R)
      let k ← liftM ($ᵗ K : ProbComp K)
      let out : R × K := (r, k)
      set (cache.cacheQuery inp out)
      return out

/-- Query implementation for the single-RO Fujisaki-Okamoto world. -/
def singleROQueryImpl {PKHash M R K : Type}
    [DecidableEq PKHash] [DecidableEq M] [SampleableType R] [SampleableType K] :
    QueryImpl (singleROOracleSpec PKHash M R K)
      (StateT (SingleROQueryCache PKHash M R K) ProbComp) :=
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (SingleROQueryCache PKHash M R K) ProbComp)
  idImpl + singleROOracleImpl (PKHash := PKHash) (M := M) (R := R) (K := K)

/-- Single-RO specialization for the `H(m)` branch. The oracle input is `(pkh pk, m)` and the
oracle output supplies both the encryption coins and the shared key. -/
def singleRO
    {PKHash : Type}
    (pke : DeterministicPKE M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (pkh : PK → PKHash)
    (rejMode : RejectionMode)
    [DecidableEq PKHash] [DecidableEq M] [DecidableEq C]
    [SampleableType M] [SampleableType R] [SampleableType K] :
    KEMScheme (OracleComp (singleROOracleSpec PKHash M R K))
      K PK ((PK × SK) × KPRF) C where
  keygen := do
    let (pk, sk) ← (monadLift pke.keygen : OracleComp (singleROOracleSpec PKHash M R K) (PK × SK))
    let kPrf ← (monadLift prf.keygen : OracleComp (singleROOracleSpec PKHash M R K) KPRF)
    return (pk, ((pk, sk), kPrf))
  encaps := fun pk => do
    let msg ← (monadLift ($ᵗ M : ProbComp M) : OracleComp (singleROOracleSpec PKHash M R K) M)
    let (r, k) ← query (spec := singleROOracleSpec PKHash M R K) (Sum.inr (pkh pk, msg))
    return (pke.encrypt pk msg r, k)
  decaps := fun ((pk, sk), kPrf) c => do
    match pke.decrypt sk c with
    | none =>
        match rejMode with
        | .explicit => return none
        | .implicit => return some (prf.eval kPrf c)
    | some msg =>
        let (r, k) ← query (spec := singleROOracleSpec PKHash M R K) (Sum.inr (pkh pk, msg))
        if h : pke.encrypt pk msg r = c then
          return some k
        else
          match rejMode with
          | .explicit => return none
          | .implicit => return some (prf.eval kPrf c)
  exec := fun comp =>
    StateT.run' (simulateQ (singleROQueryImpl (PKHash := PKHash) (M := M) (R := R) (K := K)) comp)
      ∅
  lift_probComp := monadLift
  exec_lift_probComp := by
    intro α c
    sorry

/-- Main composed Fujisaki-Okamoto theorem statement. The proof is intentionally deferred. -/
theorem IND_CCA_bound
    {M PK SK R C KD K KPRF : Type}
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    (pke : DeterministicPKE M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (kdInput : M → C → KD)
    (adversary : (FujisakiOkamoto pke prf kdInput .implicit).IND_CCA_Adversary)
    (cpaAdv₁ cpaAdv₂ : (pke.toRandomized).IND_CPA_adversary)
    (prfAdv : PRFScheme.PRFAdversary C K)
    (correctnessBound epsMsg : ℝ)
    (qHK : ℕ) :
    (FujisakiOkamoto pke prf kdInput .implicit).IND_CCA_Advantage adversary ≤
      2 * ((pke.toRandomized.IND_CPA_advantage cpaAdv₁).toReal) +
      2 * ((pke.toRandomized.IND_CPA_advantage cpaAdv₂).toReal) +
      PRFScheme.prfAdvantage prf prfAdv +
      ((2 * qHK + 3 : ℕ) : ℝ) * correctnessBound +
      2 * ((2 * qHK + 2 : ℕ) : ℝ) * epsMsg := by
  sorry

end FujisakiOkamoto
