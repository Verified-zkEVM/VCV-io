import VCVio.CryptoFoundations.FujisakiOkamoto.Defs
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.QueryTracking.RandomOracle

/-!
# Fujisaki-Okamoto T Transform

This file defines the derandomizing T transform:

- coins are derived from a random oracle on the plaintext
- decryption re-derives the coins and checks re-encryption
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

universe u v

namespace TTransform

abbrev oracleSpec (M R : Type) :=
  unifSpec + (M →ₒ R)

abbrev QueryCache (M R : Type) :=
  (M →ₒ R).QueryCache

/-- Query implementation for the T-transform oracle world: uniform sampling on the left and a lazy
random oracle on the right. -/
def queryImpl {M R : Type} [DecidableEq M] [SampleableType R] :
    QueryImpl (oracleSpec M R) (StateT (QueryCache M R) ProbComp) :=
  let ro : QueryImpl (M →ₒ R) (StateT (QueryCache M R) ProbComp) := randomOracle
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (QueryCache M R) ProbComp)
  idImpl + ro

end TTransform

open TTransform

variable {M PK SK R C : Type}

/-- Decryption for the T transform: decrypt deterministically, then re-query the coins oracle and
check that re-encryption reproduces the ciphertext. -/
def TTransform.decrypt (pke : DeterministicPKE M PK SK R C)
    [DecidableEq C] (pk : PK) (sk : SK) (c : C) :
    OracleComp (TTransform.oracleSpec M R) (Option M) := do
  match pke.decrypt sk c with
  | none => return none
  | some msg =>
      let r ← query (spec := TTransform.oracleSpec M R) (Sum.inr msg)
      return if pke.encrypt pk msg r = c then some msg else none

/-- The HHK17 T transform, realized as a monadic `AsymmEncAlg` in the random-oracle world
`unifSpec + (M →ₒ R)`. -/
def TTransform (pke : DeterministicPKE M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R] :
    AsymmEncAlg (OracleComp (TTransform.oracleSpec M R)) M PK (PK × SK) C where
  keygen := do
    let (pk, sk) ← (monadLift pke.keygen : OracleComp (TTransform.oracleSpec M R) (PK × SK))
    return (pk, (pk, sk))
  encrypt := fun pk msg => do
    let r ← query (spec := TTransform.oracleSpec M R) (Sum.inr msg)
    return pke.encrypt pk msg r
  decrypt := fun (pk, sk) c => TTransform.decrypt pke pk sk c
  exec := fun comp =>
    StateT.run' (simulateQ (TTransform.queryImpl (M := M) (R := R)) comp) ∅
  lift_probComp := monadLift
  exec_lift_probComp := by
    intro α c
    sorry

namespace TTransform

/-- The T-transform security statement. The proof is intentionally deferred. -/
theorem OW_PCVA_bound
    {M PK SK R C : Type}
    [DecidableEq M] [DecidableEq C] [SampleableType M] [SampleableType R]
    (pke : DeterministicPKE M PK SK R C)
    (adversary : OW_PCVA_Adversary (TTransform pke))
    (cpaAdv₁ cpaAdv₂ : (pke.toRandomized).IND_CPA_adversary)
    (correctnessBound gamma epsMsg : ℝ)
    (qH qP qV : ℕ) :
    (OW_PCVA_Advantage (encAlg := TTransform pke) adversary).toReal ≤
      2 * ((pke.toRandomized.IND_CPA_advantage cpaAdv₁).toReal) +
      2 * ((pke.toRandomized.IND_CPA_advantage cpaAdv₂).toReal) +
      correctnessBound +
      (qV : ℝ) * gamma +
      2 * ((qH + qP + 1 : ℕ) : ℝ) * epsMsg := by
  sorry

end TTransform
