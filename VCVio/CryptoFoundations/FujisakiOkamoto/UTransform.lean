import VCVio.CryptoFoundations.FujisakiOkamoto.TTransform
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Coercions.Add

/-!
# Fujisaki-Okamoto U Transform

This file defines the U-transform family on top of the T-transform oracle world.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

universe u v

/-- Explicit vs implicit rejection in the U transform family. -/
inductive RejectionMode where
  | explicit
  | implicit

namespace UTransform

abbrev oracleSpec (M R KD K : Type) :=
  (TTransform.oracleSpec M R) + (KD →ₒ K)

abbrev QueryCache (M R KD K : Type) :=
  TTransform.QueryCache M R × (KD →ₒ K).QueryCache

/-- Lazy random oracle for encryption coins, threaded through the combined U-transform state. -/
def coinOracleImpl {M R KD K : Type} [DecidableEq M] [SampleableType R] :
    QueryImpl (M →ₒ R) (StateT (QueryCache M R KD K) ProbComp) := fun msg => do
  let st ← get
  match st.1 msg with
  | some r => return r
  | none =>
      let r ← liftM ($ᵗ R : ProbComp R)
      set (st.1.cacheQuery msg r, st.2)
      return r

/-- Lazy random oracle for key derivation, threaded through the combined U-transform state. -/
def keyOracleImpl {M R KD K : Type} [DecidableEq KD] [SampleableType K] :
    QueryImpl (KD →ₒ K) (StateT (QueryCache M R KD K) ProbComp) := fun kd => do
  let st ← get
  match st.2 kd with
  | some k => return k
  | none =>
      let k ← liftM ($ᵗ K : ProbComp K)
      set (st.1, st.2.cacheQuery kd k)
      return k

/-- Query implementation for the full two-RO FO world. -/
def queryImpl {M R KD K : Type}
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    QueryImpl (oracleSpec M R KD K) (StateT (QueryCache M R KD K) ProbComp) :=
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (QueryCache M R KD K) ProbComp)
  ((idImpl + coinOracleImpl (M := M) (R := R) (KD := KD) (K := K)) +
    keyOracleImpl (M := M) (R := R) (KD := KD) (K := K))

end UTransform

open UTransform

variable {M PK SK R C KD K KPRF : Type}

/-- The generic two-RO U-transform family. The argument `kdInput` chooses whether the shared key
is derived from `m`, `(m, c)`, or some other encoding of the recovered plaintext and ciphertext. -/
def UTransform
    (pke : DeterministicPKE M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (kdInput : M → C → KD)
    (rejMode : RejectionMode)
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K] :
    KEMScheme (OracleComp (UTransform.oracleSpec M R KD K))
      K PK ((PK × SK) × KPRF) C where
  keygen := do
    let (pk, tsk) ←
      (monadLift (TTransform pke).keygen :
        OracleComp (UTransform.oracleSpec M R KD K) (PK × (PK × SK)))
    let kPrf ← (monadLift prf.keygen : OracleComp (UTransform.oracleSpec M R KD K) KPRF)
    return (pk, (tsk, kPrf))
  encaps := fun pk => do
    let msg ← (monadLift ($ᵗ M : ProbComp M) : OracleComp (UTransform.oracleSpec M R KD K) M)
    let c ←
      (monadLift ((TTransform pke).encrypt pk msg) :
        OracleComp (UTransform.oracleSpec M R KD K) C)
    let k ← query (spec := UTransform.oracleSpec M R KD K) (Sum.inr (kdInput msg c))
    return (c, k)
  decaps := fun ((pk, sk), kPrf) c => do
    let msg? ←
      (monadLift (TTransform.decrypt pke pk sk c) :
        OracleComp (UTransform.oracleSpec M R KD K) (Option M))
    match msg? with
    | none =>
        match rejMode with
        | .explicit => return none
        | .implicit => return some (prf.eval kPrf c)
    | some msg =>
        let k ← query (spec := UTransform.oracleSpec M R KD K) (Sum.inr (kdInput msg c))
        return some k
  exec := fun comp =>
    StateT.run' (simulateQ (UTransform.queryImpl (M := M) (R := R) (KD := KD) (K := K)) comp)
      (∅, ∅)
  lift_probComp := monadLift
  exec_lift_probComp := by
    intro α c
    sorry

namespace UTransform

/-- The generic U-transform CCA bound. The proof is intentionally deferred. -/
theorem IND_CCA_bound
    {M PK SK R C KD K KPRF : Type}
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    (pke : DeterministicPKE M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (kdInput : M → C → KD)
    (adversary : (UTransform pke prf kdInput .implicit).IND_CCA_Adversary)
    (prfAdv : PRFScheme.PRFAdversary C K)
    (owAdv : OW_PCVA_Adversary (TTransform pke))
    (correctnessBound₁ correctnessBound₂ : ℝ) :
    (UTransform pke prf kdInput .implicit).IND_CCA_Advantage adversary ≤
      PRFScheme.prfAdvantage prf prfAdv +
      correctnessBound₁ +
      correctnessBound₂ +
      (OW_PCVA_Advantage (encAlg := TTransform pke) owAdv).toReal := by
  sorry

end UTransform
